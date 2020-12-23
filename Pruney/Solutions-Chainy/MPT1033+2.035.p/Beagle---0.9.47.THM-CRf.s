%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:55 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 318 expanded)
%              Number of leaves         :   28 ( 115 expanded)
%              Depth                    :   10
%              Number of atoms          :  143 (1051 expanded)
%              Number of equality atoms :   29 ( 273 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_156,plain,(
    ! [A_51,B_52,D_53] :
      ( r2_relset_1(A_51,B_52,D_53,D_53)
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_173,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_156])).

tff(c_36,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_48,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_176,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_partfun1(C_56,A_57)
      | ~ v1_funct_2(C_56,A_57,B_58)
      | ~ v1_funct_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | v1_xboole_0(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_183,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_176])).

tff(c_200,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_183])).

tff(c_205,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_208,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_205,c_2])).

tff(c_212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_208])).

tff(c_213,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_214,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_42,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_186,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_176])).

tff(c_203,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_186])).

tff(c_215,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_215])).

tff(c_217,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_38,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_254,plain,(
    ! [D_67,C_68,A_69,B_70] :
      ( D_67 = C_68
      | ~ r1_partfun1(C_68,D_67)
      | ~ v1_partfun1(D_67,A_69)
      | ~ v1_partfun1(C_68,A_69)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ v1_funct_1(D_67)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ v1_funct_1(C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_256,plain,(
    ! [A_69,B_70] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_69)
      | ~ v1_partfun1('#skF_3',A_69)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_254])).

tff(c_259,plain,(
    ! [A_69,B_70] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_69)
      | ~ v1_partfun1('#skF_3',A_69)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_256])).

tff(c_370,plain,(
    ! [A_89,B_90] :
      ( ~ v1_partfun1('#skF_4',A_89)
      | ~ v1_partfun1('#skF_3',A_89)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(splitLeft,[status(thm)],[c_259])).

tff(c_376,plain,
    ( ~ v1_partfun1('#skF_4','#skF_1')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_46,c_370])).

tff(c_387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_213,c_217,c_376])).

tff(c_388,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_34,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_395,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_34])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_395])).

tff(c_406,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_408,plain,(
    ! [A_6] : m1_subset_1('#skF_1',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_16])).

tff(c_450,plain,(
    ! [A_95,B_96] :
      ( r1_tarski(A_95,B_96)
      | ~ m1_subset_1(A_95,k1_zfmisc_1(B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_462,plain,(
    ! [A_6] : r1_tarski('#skF_1',A_6) ),
    inference(resolution,[status(thm)],[c_408,c_450])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_424,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_406,c_14])).

tff(c_407,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_415,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_407])).

tff(c_448,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_415,c_40])).

tff(c_461,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_448,c_450])).

tff(c_481,plain,(
    ! [B_102,A_103] :
      ( B_102 = A_103
      | ~ r1_tarski(B_102,A_103)
      | ~ r1_tarski(A_103,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_485,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_461,c_481])).

tff(c_493,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_485])).

tff(c_579,plain,(
    ! [A_114] : m1_subset_1('#skF_4',k1_zfmisc_1(A_114)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_408])).

tff(c_24,plain,(
    ! [A_12,B_13,D_15] :
      ( r2_relset_1(A_12,B_13,D_15,D_15)
      | ~ m1_subset_1(D_15,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_588,plain,(
    ! [A_12,B_13] : r2_relset_1(A_12,B_13,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_579,c_24])).

tff(c_449,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_415,c_46])).

tff(c_460,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_449,c_450])).

tff(c_487,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_460,c_481])).

tff(c_496,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_487])).

tff(c_521,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_496])).

tff(c_447,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_34])).

tff(c_507,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_493,c_447])).

tff(c_595,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_507])).

tff(c_612,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_595])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.41  
% 2.77/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.42  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.77/1.42  
% 2.77/1.42  %Foreground sorts:
% 2.77/1.42  
% 2.77/1.42  
% 2.77/1.42  %Background operators:
% 2.77/1.42  
% 2.77/1.42  
% 2.77/1.42  %Foreground operators:
% 2.77/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.42  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.77/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.77/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.77/1.42  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.77/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.77/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.77/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.77/1.42  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.77/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.42  
% 2.77/1.44  tff(f_115, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_2)).
% 2.77/1.44  tff(f_61, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.77/1.44  tff(f_75, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.77/1.44  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.77/1.44  tff(f_92, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 2.77/1.44  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.77/1.44  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.77/1.44  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.77/1.44  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.77/1.44  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.77/1.44  tff(c_156, plain, (![A_51, B_52, D_53]: (r2_relset_1(A_51, B_52, D_53, D_53) | ~m1_subset_1(D_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.77/1.44  tff(c_173, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_156])).
% 2.77/1.44  tff(c_36, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.77/1.44  tff(c_62, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_36])).
% 2.77/1.44  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.77/1.44  tff(c_48, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.77/1.44  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.77/1.44  tff(c_176, plain, (![C_56, A_57, B_58]: (v1_partfun1(C_56, A_57) | ~v1_funct_2(C_56, A_57, B_58) | ~v1_funct_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | v1_xboole_0(B_58))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.77/1.44  tff(c_183, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_176])).
% 2.77/1.44  tff(c_200, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_183])).
% 2.77/1.44  tff(c_205, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_200])).
% 2.77/1.44  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.77/1.44  tff(c_208, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_205, c_2])).
% 2.77/1.44  tff(c_212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_208])).
% 2.77/1.44  tff(c_213, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_200])).
% 2.77/1.44  tff(c_214, plain, (~v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_200])).
% 2.77/1.44  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.77/1.44  tff(c_42, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.77/1.44  tff(c_186, plain, (v1_partfun1('#skF_4', '#skF_1') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_176])).
% 2.77/1.44  tff(c_203, plain, (v1_partfun1('#skF_4', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_186])).
% 2.77/1.44  tff(c_215, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_203])).
% 2.77/1.44  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_215])).
% 2.77/1.44  tff(c_217, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_203])).
% 2.77/1.44  tff(c_38, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.77/1.44  tff(c_254, plain, (![D_67, C_68, A_69, B_70]: (D_67=C_68 | ~r1_partfun1(C_68, D_67) | ~v1_partfun1(D_67, A_69) | ~v1_partfun1(C_68, A_69) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~v1_funct_1(D_67) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~v1_funct_1(C_68))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.77/1.44  tff(c_256, plain, (![A_69, B_70]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_69) | ~v1_partfun1('#skF_3', A_69) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_254])).
% 2.77/1.44  tff(c_259, plain, (![A_69, B_70]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_69) | ~v1_partfun1('#skF_3', A_69) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_256])).
% 2.77/1.44  tff(c_370, plain, (![A_89, B_90]: (~v1_partfun1('#skF_4', A_89) | ~v1_partfun1('#skF_3', A_89) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(splitLeft, [status(thm)], [c_259])).
% 2.77/1.44  tff(c_376, plain, (~v1_partfun1('#skF_4', '#skF_1') | ~v1_partfun1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_46, c_370])).
% 2.77/1.44  tff(c_387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_213, c_217, c_376])).
% 2.77/1.44  tff(c_388, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_259])).
% 2.77/1.44  tff(c_34, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.77/1.44  tff(c_395, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_388, c_34])).
% 2.77/1.44  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_395])).
% 2.77/1.44  tff(c_406, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_36])).
% 2.77/1.44  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.77/1.44  tff(c_408, plain, (![A_6]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_406, c_16])).
% 2.77/1.44  tff(c_450, plain, (![A_95, B_96]: (r1_tarski(A_95, B_96) | ~m1_subset_1(A_95, k1_zfmisc_1(B_96)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.77/1.44  tff(c_462, plain, (![A_6]: (r1_tarski('#skF_1', A_6))), inference(resolution, [status(thm)], [c_408, c_450])).
% 2.77/1.44  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.77/1.44  tff(c_424, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_406, c_406, c_14])).
% 2.77/1.44  tff(c_407, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_36])).
% 2.77/1.44  tff(c_415, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_406, c_407])).
% 2.77/1.44  tff(c_448, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_424, c_415, c_40])).
% 2.77/1.44  tff(c_461, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_448, c_450])).
% 2.77/1.44  tff(c_481, plain, (![B_102, A_103]: (B_102=A_103 | ~r1_tarski(B_102, A_103) | ~r1_tarski(A_103, B_102))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.77/1.44  tff(c_485, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_461, c_481])).
% 2.77/1.44  tff(c_493, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_462, c_485])).
% 2.77/1.44  tff(c_579, plain, (![A_114]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_114)))), inference(demodulation, [status(thm), theory('equality')], [c_493, c_408])).
% 2.77/1.44  tff(c_24, plain, (![A_12, B_13, D_15]: (r2_relset_1(A_12, B_13, D_15, D_15) | ~m1_subset_1(D_15, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.77/1.44  tff(c_588, plain, (![A_12, B_13]: (r2_relset_1(A_12, B_13, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_579, c_24])).
% 2.77/1.44  tff(c_449, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_424, c_415, c_46])).
% 2.77/1.44  tff(c_460, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_449, c_450])).
% 2.77/1.44  tff(c_487, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_460, c_481])).
% 2.77/1.44  tff(c_496, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_462, c_487])).
% 2.77/1.44  tff(c_521, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_493, c_496])).
% 2.77/1.44  tff(c_447, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_415, c_34])).
% 2.77/1.44  tff(c_507, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_493, c_493, c_447])).
% 2.77/1.44  tff(c_595, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_521, c_507])).
% 2.77/1.44  tff(c_612, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_588, c_595])).
% 2.77/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.44  
% 2.77/1.44  Inference rules
% 2.77/1.44  ----------------------
% 2.77/1.44  #Ref     : 0
% 2.77/1.44  #Sup     : 113
% 2.77/1.44  #Fact    : 0
% 2.77/1.44  #Define  : 0
% 2.77/1.44  #Split   : 8
% 2.77/1.44  #Chain   : 0
% 2.77/1.44  #Close   : 0
% 2.77/1.44  
% 2.77/1.44  Ordering : KBO
% 2.77/1.44  
% 2.77/1.44  Simplification rules
% 2.77/1.44  ----------------------
% 2.77/1.44  #Subsume      : 9
% 2.77/1.44  #Demod        : 116
% 2.77/1.44  #Tautology    : 74
% 2.77/1.44  #SimpNegUnit  : 4
% 2.77/1.44  #BackRed      : 32
% 2.77/1.44  
% 2.77/1.44  #Partial instantiations: 0
% 2.77/1.44  #Strategies tried      : 1
% 2.77/1.44  
% 2.77/1.44  Timing (in seconds)
% 2.77/1.44  ----------------------
% 2.77/1.44  Preprocessing        : 0.33
% 2.77/1.44  Parsing              : 0.18
% 2.77/1.44  CNF conversion       : 0.02
% 2.77/1.44  Main loop            : 0.33
% 2.77/1.44  Inferencing          : 0.12
% 2.77/1.44  Reduction            : 0.11
% 2.77/1.44  Demodulation         : 0.08
% 2.77/1.44  BG Simplification    : 0.02
% 2.77/1.44  Subsumption          : 0.05
% 2.77/1.44  Abstraction          : 0.01
% 2.77/1.44  MUC search           : 0.00
% 2.77/1.44  Cooper               : 0.00
% 2.77/1.44  Total                : 0.70
% 2.77/1.44  Index Insertion      : 0.00
% 2.77/1.44  Index Deletion       : 0.00
% 2.77/1.44  Index Matching       : 0.00
% 2.77/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
