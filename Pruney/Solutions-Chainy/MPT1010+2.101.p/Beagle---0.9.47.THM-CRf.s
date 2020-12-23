%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:18 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   71 (  96 expanded)
%              Number of leaves         :   38 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 180 expanded)
%              Number of equality atoms :   27 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_95,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_42,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_50,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_111,plain,(
    ! [C_50,B_51,A_52] :
      ( v5_relat_1(C_50,B_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_52,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_115,plain,(
    v5_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_111])).

tff(c_52,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_28,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_86,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_89,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_54,c_86])).

tff(c_92,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_89])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_56,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_123,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_127,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_123])).

tff(c_197,plain,(
    ! [B_83,A_84,C_85] :
      ( k1_xboole_0 = B_83
      | k1_relset_1(A_84,B_83,C_85) = A_84
      | ~ v1_funct_2(C_85,A_84,B_83)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_200,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_197])).

tff(c_203,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_127,c_200])).

tff(c_204,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_30,plain,(
    ! [C_22,B_21,A_20] :
      ( m1_subset_1(k1_funct_1(C_22,B_21),A_20)
      | ~ r2_hidden(B_21,k1_relat_1(C_22))
      | ~ v1_funct_1(C_22)
      | ~ v5_relat_1(C_22,A_20)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_208,plain,(
    ! [B_21,A_20] :
      ( m1_subset_1(k1_funct_1('#skF_6',B_21),A_20)
      | ~ r2_hidden(B_21,'#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_20)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_30])).

tff(c_218,plain,(
    ! [B_86,A_87] :
      ( m1_subset_1(k1_funct_1('#skF_6',B_86),A_87)
      | ~ r2_hidden(B_86,'#skF_3')
      | ~ v5_relat_1('#skF_6',A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_58,c_208])).

tff(c_22,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_tarski(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_93,plain,(
    ! [A_43,B_44] :
      ( r2_hidden(A_43,B_44)
      | v1_xboole_0(B_44)
      | ~ m1_subset_1(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_97,plain,(
    ! [A_43,A_1] :
      ( A_43 = A_1
      | v1_xboole_0(k1_tarski(A_1))
      | ~ m1_subset_1(A_43,k1_tarski(A_1)) ) ),
    inference(resolution,[status(thm)],[c_93,c_4])).

tff(c_100,plain,(
    ! [A_43,A_1] :
      ( A_43 = A_1
      | ~ m1_subset_1(A_43,k1_tarski(A_1)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_97])).

tff(c_264,plain,(
    ! [B_88,A_89] :
      ( k1_funct_1('#skF_6',B_88) = A_89
      | ~ r2_hidden(B_88,'#skF_3')
      | ~ v5_relat_1('#skF_6',k1_tarski(A_89)) ) ),
    inference(resolution,[status(thm)],[c_218,c_100])).

tff(c_280,plain,(
    ! [A_90] :
      ( k1_funct_1('#skF_6','#skF_5') = A_90
      | ~ v5_relat_1('#skF_6',k1_tarski(A_90)) ) ),
    inference(resolution,[status(thm)],[c_52,c_264])).

tff(c_283,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_115,c_280])).

tff(c_287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_283])).

tff(c_288,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_314,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_22])).

tff(c_322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.32  
% 2.51/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.32  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.51/1.32  
% 2.51/1.32  %Foreground sorts:
% 2.51/1.32  
% 2.51/1.32  
% 2.51/1.32  %Background operators:
% 2.51/1.32  
% 2.51/1.32  
% 2.51/1.32  %Foreground operators:
% 2.51/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.51/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.51/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.51/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.51/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.51/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.51/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.51/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.51/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.51/1.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.51/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.51/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.51/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.51/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.51/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.51/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.51/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.51/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.51/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.51/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.32  
% 2.51/1.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.51/1.34  tff(f_106, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.51/1.34  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.51/1.34  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.51/1.34  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.51/1.34  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.51/1.34  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.51/1.34  tff(f_67, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 2.51/1.34  tff(f_42, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.51/1.34  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.51/1.34  tff(f_33, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.51/1.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.51/1.34  tff(c_50, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.51/1.34  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.51/1.34  tff(c_111, plain, (![C_50, B_51, A_52]: (v5_relat_1(C_50, B_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_52, B_51))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.51/1.34  tff(c_115, plain, (v5_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_111])).
% 2.51/1.34  tff(c_52, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.51/1.34  tff(c_28, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.51/1.34  tff(c_86, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.51/1.34  tff(c_89, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_54, c_86])).
% 2.51/1.34  tff(c_92, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_89])).
% 2.51/1.34  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.51/1.34  tff(c_56, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.51/1.34  tff(c_123, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.51/1.34  tff(c_127, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_123])).
% 2.51/1.34  tff(c_197, plain, (![B_83, A_84, C_85]: (k1_xboole_0=B_83 | k1_relset_1(A_84, B_83, C_85)=A_84 | ~v1_funct_2(C_85, A_84, B_83) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.51/1.34  tff(c_200, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_197])).
% 2.51/1.34  tff(c_203, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_127, c_200])).
% 2.51/1.34  tff(c_204, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_203])).
% 2.51/1.34  tff(c_30, plain, (![C_22, B_21, A_20]: (m1_subset_1(k1_funct_1(C_22, B_21), A_20) | ~r2_hidden(B_21, k1_relat_1(C_22)) | ~v1_funct_1(C_22) | ~v5_relat_1(C_22, A_20) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.51/1.34  tff(c_208, plain, (![B_21, A_20]: (m1_subset_1(k1_funct_1('#skF_6', B_21), A_20) | ~r2_hidden(B_21, '#skF_3') | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_20) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_204, c_30])).
% 2.51/1.34  tff(c_218, plain, (![B_86, A_87]: (m1_subset_1(k1_funct_1('#skF_6', B_86), A_87) | ~r2_hidden(B_86, '#skF_3') | ~v5_relat_1('#skF_6', A_87))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_58, c_208])).
% 2.51/1.34  tff(c_22, plain, (![A_12]: (~v1_xboole_0(k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.51/1.34  tff(c_93, plain, (![A_43, B_44]: (r2_hidden(A_43, B_44) | v1_xboole_0(B_44) | ~m1_subset_1(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.51/1.34  tff(c_4, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.51/1.34  tff(c_97, plain, (![A_43, A_1]: (A_43=A_1 | v1_xboole_0(k1_tarski(A_1)) | ~m1_subset_1(A_43, k1_tarski(A_1)))), inference(resolution, [status(thm)], [c_93, c_4])).
% 2.51/1.34  tff(c_100, plain, (![A_43, A_1]: (A_43=A_1 | ~m1_subset_1(A_43, k1_tarski(A_1)))), inference(negUnitSimplification, [status(thm)], [c_22, c_97])).
% 2.51/1.34  tff(c_264, plain, (![B_88, A_89]: (k1_funct_1('#skF_6', B_88)=A_89 | ~r2_hidden(B_88, '#skF_3') | ~v5_relat_1('#skF_6', k1_tarski(A_89)))), inference(resolution, [status(thm)], [c_218, c_100])).
% 2.51/1.34  tff(c_280, plain, (![A_90]: (k1_funct_1('#skF_6', '#skF_5')=A_90 | ~v5_relat_1('#skF_6', k1_tarski(A_90)))), inference(resolution, [status(thm)], [c_52, c_264])).
% 2.51/1.34  tff(c_283, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_115, c_280])).
% 2.51/1.34  tff(c_287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_283])).
% 2.51/1.34  tff(c_288, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_203])).
% 2.51/1.34  tff(c_314, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_288, c_22])).
% 2.51/1.34  tff(c_322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_314])).
% 2.51/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.34  
% 2.51/1.34  Inference rules
% 2.51/1.34  ----------------------
% 2.51/1.34  #Ref     : 0
% 2.51/1.34  #Sup     : 55
% 2.51/1.34  #Fact    : 0
% 2.51/1.34  #Define  : 0
% 2.51/1.34  #Split   : 1
% 2.51/1.34  #Chain   : 0
% 2.51/1.34  #Close   : 0
% 2.51/1.34  
% 2.51/1.34  Ordering : KBO
% 2.51/1.34  
% 2.51/1.34  Simplification rules
% 2.51/1.34  ----------------------
% 2.51/1.34  #Subsume      : 0
% 2.51/1.34  #Demod        : 21
% 2.51/1.34  #Tautology    : 19
% 2.51/1.34  #SimpNegUnit  : 3
% 2.51/1.34  #BackRed      : 5
% 2.51/1.34  
% 2.51/1.34  #Partial instantiations: 0
% 2.51/1.34  #Strategies tried      : 1
% 2.51/1.34  
% 2.51/1.34  Timing (in seconds)
% 2.51/1.34  ----------------------
% 2.51/1.34  Preprocessing        : 0.34
% 2.51/1.34  Parsing              : 0.18
% 2.51/1.34  CNF conversion       : 0.02
% 2.51/1.34  Main loop            : 0.23
% 2.51/1.34  Inferencing          : 0.08
% 2.51/1.34  Reduction            : 0.07
% 2.51/1.34  Demodulation         : 0.05
% 2.51/1.34  BG Simplification    : 0.02
% 2.51/1.34  Subsumption          : 0.04
% 2.51/1.34  Abstraction          : 0.02
% 2.51/1.34  MUC search           : 0.00
% 2.51/1.34  Cooper               : 0.00
% 2.51/1.34  Total                : 0.60
% 2.51/1.34  Index Insertion      : 0.00
% 2.51/1.34  Index Deletion       : 0.00
% 2.51/1.34  Index Matching       : 0.00
% 2.51/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
