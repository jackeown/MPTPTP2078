%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:11 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   70 (  96 expanded)
%              Number of leaves         :   37 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :   96 ( 181 expanded)
%              Number of equality atoms :   33 (  63 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_121,plain,(
    ! [C_51,B_52,A_53] :
      ( v5_relat_1(C_51,B_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_53,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_125,plain,(
    v5_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_121])).

tff(c_54,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_116,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_120,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_116])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_58,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_160,plain,(
    ! [A_65,B_66,C_67] :
      ( k1_relset_1(A_65,B_66,C_67) = k1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_164,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_160])).

tff(c_213,plain,(
    ! [B_98,A_99,C_100] :
      ( k1_xboole_0 = B_98
      | k1_relset_1(A_99,B_98,C_100) = A_99
      | ~ v1_funct_2(C_100,A_99,B_98)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_99,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_216,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_213])).

tff(c_219,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_164,c_216])).

tff(c_220,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_176,plain,(
    ! [B_84,C_85,A_86] :
      ( r2_hidden(k1_funct_1(B_84,C_85),A_86)
      | ~ r2_hidden(C_85,k1_relat_1(B_84))
      | ~ v1_funct_1(B_84)
      | ~ v5_relat_1(B_84,A_86)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_131,plain,(
    ! [D_57,B_58,A_59] :
      ( D_57 = B_58
      | D_57 = A_59
      | ~ r2_hidden(D_57,k2_tarski(A_59,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_140,plain,(
    ! [D_57,A_8] :
      ( D_57 = A_8
      | D_57 = A_8
      | ~ r2_hidden(D_57,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_131])).

tff(c_188,plain,(
    ! [B_84,C_85,A_8] :
      ( k1_funct_1(B_84,C_85) = A_8
      | ~ r2_hidden(C_85,k1_relat_1(B_84))
      | ~ v1_funct_1(B_84)
      | ~ v5_relat_1(B_84,k1_tarski(A_8))
      | ~ v1_relat_1(B_84) ) ),
    inference(resolution,[status(thm)],[c_176,c_140])).

tff(c_224,plain,(
    ! [C_85,A_8] :
      ( k1_funct_1('#skF_6',C_85) = A_8
      | ~ r2_hidden(C_85,'#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',k1_tarski(A_8))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_188])).

tff(c_679,plain,(
    ! [C_1253,A_1254] :
      ( k1_funct_1('#skF_6',C_1253) = A_1254
      | ~ r2_hidden(C_1253,'#skF_3')
      | ~ v5_relat_1('#skF_6',k1_tarski(A_1254)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_60,c_224])).

tff(c_687,plain,(
    ! [A_1280] :
      ( k1_funct_1('#skF_6','#skF_5') = A_1280
      | ~ v5_relat_1('#skF_6',k1_tarski(A_1280)) ) ),
    inference(resolution,[status(thm)],[c_54,c_679])).

tff(c_691,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_125,c_687])).

tff(c_695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_691])).

tff(c_696,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_71,plain,(
    ! [D_34,A_35] : r2_hidden(D_34,k2_tarski(A_35,D_34)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_74,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_71])).

tff(c_81,plain,(
    ! [B_39,A_40] :
      ( ~ r1_tarski(B_39,A_40)
      | ~ r2_hidden(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_95,plain,(
    ! [A_8] : ~ r1_tarski(k1_tarski(A_8),A_8) ),
    inference(resolution,[status(thm)],[c_74,c_81])).

tff(c_708,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_696,c_95])).

tff(c_716,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_708])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:31:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.40  
% 2.82/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.41  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.82/1.41  
% 2.82/1.41  %Foreground sorts:
% 2.82/1.41  
% 2.82/1.41  
% 2.82/1.41  %Background operators:
% 2.82/1.41  
% 2.82/1.41  
% 2.82/1.41  %Foreground operators:
% 2.82/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.82/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.82/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.82/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.82/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.82/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.82/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.82/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.82/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.82/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.82/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.82/1.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.82/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.82/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.82/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.82/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.82/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.82/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.82/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.41  
% 2.82/1.42  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.82/1.42  tff(f_101, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.82/1.42  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.82/1.42  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.82/1.42  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.82/1.42  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.82/1.42  tff(f_53, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 2.82/1.42  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.82/1.42  tff(f_36, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.82/1.42  tff(f_58, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.82/1.42  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.82/1.42  tff(c_52, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.82/1.42  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.82/1.42  tff(c_121, plain, (![C_51, B_52, A_53]: (v5_relat_1(C_51, B_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_53, B_52))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.82/1.42  tff(c_125, plain, (v5_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_121])).
% 2.82/1.42  tff(c_54, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.82/1.42  tff(c_116, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.82/1.42  tff(c_120, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_116])).
% 2.82/1.42  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.82/1.42  tff(c_58, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.82/1.42  tff(c_160, plain, (![A_65, B_66, C_67]: (k1_relset_1(A_65, B_66, C_67)=k1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.82/1.42  tff(c_164, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_160])).
% 2.82/1.42  tff(c_213, plain, (![B_98, A_99, C_100]: (k1_xboole_0=B_98 | k1_relset_1(A_99, B_98, C_100)=A_99 | ~v1_funct_2(C_100, A_99, B_98) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_99, B_98))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.82/1.42  tff(c_216, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_213])).
% 2.82/1.42  tff(c_219, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_164, c_216])).
% 2.82/1.42  tff(c_220, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_219])).
% 2.82/1.42  tff(c_176, plain, (![B_84, C_85, A_86]: (r2_hidden(k1_funct_1(B_84, C_85), A_86) | ~r2_hidden(C_85, k1_relat_1(B_84)) | ~v1_funct_1(B_84) | ~v5_relat_1(B_84, A_86) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.82/1.42  tff(c_22, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.82/1.42  tff(c_131, plain, (![D_57, B_58, A_59]: (D_57=B_58 | D_57=A_59 | ~r2_hidden(D_57, k2_tarski(A_59, B_58)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.82/1.42  tff(c_140, plain, (![D_57, A_8]: (D_57=A_8 | D_57=A_8 | ~r2_hidden(D_57, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_131])).
% 2.82/1.42  tff(c_188, plain, (![B_84, C_85, A_8]: (k1_funct_1(B_84, C_85)=A_8 | ~r2_hidden(C_85, k1_relat_1(B_84)) | ~v1_funct_1(B_84) | ~v5_relat_1(B_84, k1_tarski(A_8)) | ~v1_relat_1(B_84))), inference(resolution, [status(thm)], [c_176, c_140])).
% 2.82/1.42  tff(c_224, plain, (![C_85, A_8]: (k1_funct_1('#skF_6', C_85)=A_8 | ~r2_hidden(C_85, '#skF_3') | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', k1_tarski(A_8)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_220, c_188])).
% 2.82/1.42  tff(c_679, plain, (![C_1253, A_1254]: (k1_funct_1('#skF_6', C_1253)=A_1254 | ~r2_hidden(C_1253, '#skF_3') | ~v5_relat_1('#skF_6', k1_tarski(A_1254)))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_60, c_224])).
% 2.82/1.42  tff(c_687, plain, (![A_1280]: (k1_funct_1('#skF_6', '#skF_5')=A_1280 | ~v5_relat_1('#skF_6', k1_tarski(A_1280)))), inference(resolution, [status(thm)], [c_54, c_679])).
% 2.82/1.42  tff(c_691, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_125, c_687])).
% 2.82/1.42  tff(c_695, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_691])).
% 2.82/1.42  tff(c_696, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_219])).
% 2.82/1.42  tff(c_71, plain, (![D_34, A_35]: (r2_hidden(D_34, k2_tarski(A_35, D_34)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.82/1.42  tff(c_74, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_71])).
% 2.82/1.42  tff(c_81, plain, (![B_39, A_40]: (~r1_tarski(B_39, A_40) | ~r2_hidden(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.82/1.42  tff(c_95, plain, (![A_8]: (~r1_tarski(k1_tarski(A_8), A_8))), inference(resolution, [status(thm)], [c_74, c_81])).
% 2.82/1.42  tff(c_708, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_696, c_95])).
% 2.82/1.42  tff(c_716, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_708])).
% 2.82/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.42  
% 2.82/1.42  Inference rules
% 2.82/1.42  ----------------------
% 2.82/1.42  #Ref     : 0
% 2.82/1.42  #Sup     : 89
% 2.82/1.42  #Fact    : 2
% 2.82/1.42  #Define  : 0
% 2.82/1.42  #Split   : 2
% 2.82/1.42  #Chain   : 0
% 2.82/1.42  #Close   : 0
% 2.82/1.42  
% 2.82/1.42  Ordering : KBO
% 2.82/1.42  
% 2.82/1.42  Simplification rules
% 2.82/1.42  ----------------------
% 2.82/1.42  #Subsume      : 6
% 2.82/1.42  #Demod        : 17
% 2.82/1.42  #Tautology    : 22
% 2.82/1.42  #SimpNegUnit  : 1
% 2.82/1.42  #BackRed      : 5
% 2.82/1.42  
% 2.82/1.42  #Partial instantiations: 736
% 2.82/1.42  #Strategies tried      : 1
% 2.82/1.42  
% 2.82/1.42  Timing (in seconds)
% 2.82/1.42  ----------------------
% 2.82/1.42  Preprocessing        : 0.34
% 2.82/1.42  Parsing              : 0.17
% 2.82/1.42  CNF conversion       : 0.02
% 2.82/1.42  Main loop            : 0.33
% 2.82/1.42  Inferencing          : 0.16
% 2.82/1.42  Reduction            : 0.08
% 2.82/1.42  Demodulation         : 0.06
% 2.82/1.42  BG Simplification    : 0.02
% 2.82/1.42  Subsumption          : 0.05
% 2.82/1.42  Abstraction          : 0.02
% 2.82/1.42  MUC search           : 0.00
% 2.82/1.42  Cooper               : 0.00
% 2.82/1.42  Total                : 0.69
% 2.82/1.42  Index Insertion      : 0.00
% 2.82/1.42  Index Deletion       : 0.00
% 2.82/1.42  Index Matching       : 0.00
% 2.82/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
