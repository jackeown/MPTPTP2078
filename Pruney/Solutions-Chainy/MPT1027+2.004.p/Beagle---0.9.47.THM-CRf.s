%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:42 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 129 expanded)
%              Number of leaves         :   32 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :   99 ( 319 expanded)
%              Number of equality atoms :   23 (  74 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_100,axiom,(
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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_50,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_58,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50])).

tff(c_52,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_202,plain,(
    ! [B_75,C_76,A_77] :
      ( k1_xboole_0 = B_75
      | v1_funct_2(C_76,A_77,B_75)
      | k1_relset_1(A_77,B_75,C_76) != A_77
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_205,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_202])).

tff(c_214,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_205])).

tff(c_215,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_214])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_115,plain,(
    ! [B_42,A_43] :
      ( ~ r1_xboole_0(B_42,A_43)
      | ~ r1_tarski(B_42,A_43)
      | v1_xboole_0(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_120,plain,(
    ! [A_44] :
      ( ~ r1_tarski(A_44,k1_xboole_0)
      | v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_4,c_115])).

tff(c_125,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_120])).

tff(c_226,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_125])).

tff(c_22,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_229,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_215,c_22])).

tff(c_109,plain,(
    ! [B_40,A_41] :
      ( v1_xboole_0(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_113,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_109])).

tff(c_114,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_271,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_114])).

tff(c_275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_271])).

tff(c_276,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_303,plain,(
    ! [A_90,B_91,C_92] :
      ( k1_relset_1(A_90,B_91,C_92) = k1_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_306,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_303])).

tff(c_314,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_306])).

tff(c_28,plain,(
    ! [A_15] :
      ( v1_xboole_0(k1_relat_1(A_15))
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_318,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_28])).

tff(c_322,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_318])).

tff(c_290,plain,(
    ! [C_87,A_88,B_89] :
      ( v1_partfun1(C_87,A_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ v1_xboole_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_300,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_290])).

tff(c_325,plain,(
    v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_300])).

tff(c_353,plain,(
    ! [C_114,A_115,B_116] :
      ( v1_funct_2(C_114,A_115,B_116)
      | ~ v1_partfun1(C_114,A_115)
      | ~ v1_funct_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_356,plain,
    ( v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_353])).

tff(c_365,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_325,c_356])).

tff(c_367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_365])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:21:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.29  
% 2.19/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.30  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.19/1.30  
% 2.19/1.30  %Foreground sorts:
% 2.19/1.30  
% 2.19/1.30  
% 2.19/1.30  %Background operators:
% 2.19/1.30  
% 2.19/1.30  
% 2.19/1.30  %Foreground operators:
% 2.19/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.19/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.19/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.19/1.30  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.19/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.19/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.19/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.19/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.19/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.19/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.30  
% 2.19/1.31  tff(f_113, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 2.19/1.31  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.19/1.31  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.19/1.31  tff(f_29, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.19/1.31  tff(f_37, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.19/1.31  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.19/1.31  tff(f_57, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.19/1.31  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.19/1.31  tff(f_61, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.19/1.31  tff(f_82, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 2.19/1.31  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 2.19/1.31  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.19/1.31  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.19/1.31  tff(c_50, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.19/1.31  tff(c_58, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50])).
% 2.19/1.31  tff(c_52, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.19/1.31  tff(c_202, plain, (![B_75, C_76, A_77]: (k1_xboole_0=B_75 | v1_funct_2(C_76, A_77, B_75) | k1_relset_1(A_77, B_75, C_76)!=A_77 | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_75))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.19/1.31  tff(c_205, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_54, c_202])).
% 2.19/1.31  tff(c_214, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_205])).
% 2.19/1.31  tff(c_215, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_58, c_214])).
% 2.19/1.31  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.19/1.31  tff(c_4, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.19/1.31  tff(c_115, plain, (![B_42, A_43]: (~r1_xboole_0(B_42, A_43) | ~r1_tarski(B_42, A_43) | v1_xboole_0(B_42))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.31  tff(c_120, plain, (![A_44]: (~r1_tarski(A_44, k1_xboole_0) | v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_4, c_115])).
% 2.19/1.31  tff(c_125, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_120])).
% 2.19/1.31  tff(c_226, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_125])).
% 2.19/1.31  tff(c_22, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.19/1.31  tff(c_229, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_215, c_22])).
% 2.19/1.31  tff(c_109, plain, (![B_40, A_41]: (v1_xboole_0(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.19/1.31  tff(c_113, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_109])).
% 2.19/1.31  tff(c_114, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_113])).
% 2.19/1.31  tff(c_271, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_229, c_114])).
% 2.54/1.31  tff(c_275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_226, c_271])).
% 2.54/1.31  tff(c_276, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_113])).
% 2.54/1.31  tff(c_303, plain, (![A_90, B_91, C_92]: (k1_relset_1(A_90, B_91, C_92)=k1_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.54/1.31  tff(c_306, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_303])).
% 2.54/1.31  tff(c_314, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_306])).
% 2.54/1.31  tff(c_28, plain, (![A_15]: (v1_xboole_0(k1_relat_1(A_15)) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.54/1.31  tff(c_318, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_314, c_28])).
% 2.54/1.31  tff(c_322, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_318])).
% 2.54/1.31  tff(c_290, plain, (![C_87, A_88, B_89]: (v1_partfun1(C_87, A_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~v1_xboole_0(A_88))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.54/1.31  tff(c_300, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_290])).
% 2.54/1.31  tff(c_325, plain, (v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_322, c_300])).
% 2.54/1.31  tff(c_353, plain, (![C_114, A_115, B_116]: (v1_funct_2(C_114, A_115, B_116) | ~v1_partfun1(C_114, A_115) | ~v1_funct_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.54/1.31  tff(c_356, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_353])).
% 2.54/1.31  tff(c_365, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_325, c_356])).
% 2.54/1.31  tff(c_367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_365])).
% 2.54/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.31  
% 2.54/1.31  Inference rules
% 2.54/1.31  ----------------------
% 2.54/1.31  #Ref     : 0
% 2.54/1.31  #Sup     : 59
% 2.54/1.31  #Fact    : 0
% 2.54/1.31  #Define  : 0
% 2.54/1.31  #Split   : 4
% 2.54/1.31  #Chain   : 0
% 2.54/1.31  #Close   : 0
% 2.54/1.31  
% 2.54/1.31  Ordering : KBO
% 2.54/1.31  
% 2.54/1.31  Simplification rules
% 2.54/1.31  ----------------------
% 2.54/1.31  #Subsume      : 2
% 2.54/1.31  #Demod        : 55
% 2.54/1.31  #Tautology    : 21
% 2.54/1.31  #SimpNegUnit  : 4
% 2.54/1.31  #BackRed      : 18
% 2.54/1.31  
% 2.54/1.31  #Partial instantiations: 0
% 2.54/1.31  #Strategies tried      : 1
% 2.54/1.31  
% 2.54/1.31  Timing (in seconds)
% 2.54/1.31  ----------------------
% 2.54/1.31  Preprocessing        : 0.31
% 2.54/1.31  Parsing              : 0.16
% 2.54/1.31  CNF conversion       : 0.02
% 2.54/1.31  Main loop            : 0.24
% 2.54/1.31  Inferencing          : 0.09
% 2.54/1.31  Reduction            : 0.08
% 2.54/1.31  Demodulation         : 0.05
% 2.54/1.31  BG Simplification    : 0.02
% 2.54/1.32  Subsumption          : 0.04
% 2.54/1.32  Abstraction          : 0.01
% 2.54/1.32  MUC search           : 0.00
% 2.54/1.32  Cooper               : 0.00
% 2.54/1.32  Total                : 0.59
% 2.54/1.32  Index Insertion      : 0.00
% 2.54/1.32  Index Deletion       : 0.00
% 2.54/1.32  Index Matching       : 0.00
% 2.54/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
