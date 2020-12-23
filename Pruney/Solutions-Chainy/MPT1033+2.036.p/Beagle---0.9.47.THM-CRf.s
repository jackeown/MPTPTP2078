%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:55 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 388 expanded)
%              Number of leaves         :   28 ( 136 expanded)
%              Depth                    :   12
%              Number of atoms          :  150 (1242 expanded)
%              Number of equality atoms :   28 ( 345 expanded)
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

tff(f_113,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_73,axiom,(
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

tff(f_90,axiom,(
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

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_193,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( r2_relset_1(A_54,B_55,C_56,C_56)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_214,plain,(
    ! [C_58] :
      ( r2_relset_1('#skF_1','#skF_2',C_58,C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_44,c_193])).

tff(c_227,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_214])).

tff(c_34,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_51,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_46,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_154,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_partfun1(C_51,A_52)
      | ~ v1_funct_2(C_51,A_52,B_53)
      | ~ v1_funct_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | v1_xboole_0(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_161,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_154])).

tff(c_178,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_161])).

tff(c_183,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_186,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_183,c_2])).

tff(c_190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_186])).

tff(c_191,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_192,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_40,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_164,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_154])).

tff(c_181,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_164])).

tff(c_213,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_181])).

tff(c_36,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_247,plain,(
    ! [D_60,C_61,A_62,B_63] :
      ( D_60 = C_61
      | ~ r1_partfun1(C_61,D_60)
      | ~ v1_partfun1(D_60,A_62)
      | ~ v1_partfun1(C_61,A_62)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ v1_funct_1(D_60)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ v1_funct_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_249,plain,(
    ! [A_62,B_63] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_62)
      | ~ v1_partfun1('#skF_3',A_62)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_247])).

tff(c_252,plain,(
    ! [A_62,B_63] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_62)
      | ~ v1_partfun1('#skF_3',A_62)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_249])).

tff(c_340,plain,(
    ! [A_82,B_83] :
      ( ~ v1_partfun1('#skF_4',A_82)
      | ~ v1_partfun1('#skF_3',A_82)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_346,plain,
    ( ~ v1_partfun1('#skF_4','#skF_1')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_44,c_340])).

tff(c_357,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_191,c_213,c_346])).

tff(c_358,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_32,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_365,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_32])).

tff(c_375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_365])).

tff(c_376,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_390,plain,(
    ! [A_6] : m1_subset_1('#skF_1',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_16])).

tff(c_421,plain,(
    ! [A_90,B_91] :
      ( r1_tarski(A_90,B_91)
      | ~ m1_subset_1(A_90,k1_zfmisc_1(B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_437,plain,(
    ! [A_6] : r1_tarski('#skF_1',A_6) ),
    inference(resolution,[status(thm)],[c_390,c_421])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_392,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_376,c_12])).

tff(c_377,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_382,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_377])).

tff(c_419,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_382,c_38])).

tff(c_435,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_419,c_421])).

tff(c_438,plain,(
    ! [B_92,A_93] :
      ( B_92 = A_93
      | ~ r1_tarski(B_92,A_93)
      | ~ r1_tarski(A_93,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_443,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_435,c_438])).

tff(c_456,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_443])).

tff(c_467,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_390])).

tff(c_575,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( r2_relset_1(A_106,B_107,C_108,C_108)
      | ~ m1_subset_1(D_109,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107)))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_591,plain,(
    ! [A_115,B_116,C_117] :
      ( r2_relset_1(A_115,B_116,C_117,C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(resolution,[status(thm)],[c_467,c_575])).

tff(c_602,plain,(
    ! [A_115,B_116] : r2_relset_1(A_115,B_116,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_467,c_591])).

tff(c_457,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_437])).

tff(c_418,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_382,c_44])).

tff(c_436,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_418,c_421])).

tff(c_458,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_436])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_489,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_458,c_4])).

tff(c_492,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_489])).

tff(c_417,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_32])).

tff(c_462,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_456,c_417])).

tff(c_572,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_462])).

tff(c_606,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_572])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.40  
% 2.78/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.41  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.78/1.41  
% 2.78/1.41  %Foreground sorts:
% 2.78/1.41  
% 2.78/1.41  
% 2.78/1.41  %Background operators:
% 2.78/1.41  
% 2.78/1.41  
% 2.78/1.41  %Foreground operators:
% 2.78/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.78/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.41  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.78/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.78/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.41  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.78/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.78/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.78/1.41  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.78/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.41  
% 2.78/1.42  tff(f_113, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_2)).
% 2.78/1.42  tff(f_59, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.78/1.42  tff(f_73, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.78/1.42  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.78/1.42  tff(f_90, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 2.78/1.42  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.78/1.42  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.78/1.42  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.78/1.42  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.78/1.42  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.42  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.42  tff(c_193, plain, (![A_54, B_55, C_56, D_57]: (r2_relset_1(A_54, B_55, C_56, C_56) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.78/1.42  tff(c_214, plain, (![C_58]: (r2_relset_1('#skF_1', '#skF_2', C_58, C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_44, c_193])).
% 2.78/1.42  tff(c_227, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_214])).
% 2.78/1.42  tff(c_34, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.42  tff(c_51, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_34])).
% 2.78/1.42  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.42  tff(c_46, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.42  tff(c_154, plain, (![C_51, A_52, B_53]: (v1_partfun1(C_51, A_52) | ~v1_funct_2(C_51, A_52, B_53) | ~v1_funct_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | v1_xboole_0(B_53))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.78/1.42  tff(c_161, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_154])).
% 2.78/1.42  tff(c_178, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_161])).
% 2.78/1.42  tff(c_183, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_178])).
% 2.78/1.42  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.78/1.42  tff(c_186, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_183, c_2])).
% 2.78/1.42  tff(c_190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_186])).
% 2.78/1.42  tff(c_191, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_178])).
% 2.78/1.42  tff(c_192, plain, (~v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_178])).
% 2.78/1.42  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.42  tff(c_40, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.42  tff(c_164, plain, (v1_partfun1('#skF_4', '#skF_1') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_154])).
% 2.78/1.42  tff(c_181, plain, (v1_partfun1('#skF_4', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_164])).
% 2.78/1.42  tff(c_213, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_192, c_181])).
% 2.78/1.42  tff(c_36, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.42  tff(c_247, plain, (![D_60, C_61, A_62, B_63]: (D_60=C_61 | ~r1_partfun1(C_61, D_60) | ~v1_partfun1(D_60, A_62) | ~v1_partfun1(C_61, A_62) | ~m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~v1_funct_1(D_60) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~v1_funct_1(C_61))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.78/1.42  tff(c_249, plain, (![A_62, B_63]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_62) | ~v1_partfun1('#skF_3', A_62) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_247])).
% 2.78/1.42  tff(c_252, plain, (![A_62, B_63]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_62) | ~v1_partfun1('#skF_3', A_62) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_249])).
% 2.78/1.42  tff(c_340, plain, (![A_82, B_83]: (~v1_partfun1('#skF_4', A_82) | ~v1_partfun1('#skF_3', A_82) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(splitLeft, [status(thm)], [c_252])).
% 2.78/1.42  tff(c_346, plain, (~v1_partfun1('#skF_4', '#skF_1') | ~v1_partfun1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_44, c_340])).
% 2.78/1.42  tff(c_357, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_191, c_213, c_346])).
% 2.78/1.42  tff(c_358, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_252])).
% 2.78/1.42  tff(c_32, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.42  tff(c_365, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_358, c_32])).
% 2.78/1.42  tff(c_375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_227, c_365])).
% 2.78/1.42  tff(c_376, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_34])).
% 2.78/1.42  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.78/1.42  tff(c_390, plain, (![A_6]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_376, c_16])).
% 2.78/1.42  tff(c_421, plain, (![A_90, B_91]: (r1_tarski(A_90, B_91) | ~m1_subset_1(A_90, k1_zfmisc_1(B_91)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.78/1.42  tff(c_437, plain, (![A_6]: (r1_tarski('#skF_1', A_6))), inference(resolution, [status(thm)], [c_390, c_421])).
% 2.78/1.42  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.78/1.42  tff(c_392, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_376, c_376, c_12])).
% 2.78/1.42  tff(c_377, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_34])).
% 2.78/1.42  tff(c_382, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_376, c_377])).
% 2.78/1.42  tff(c_419, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_392, c_382, c_38])).
% 2.78/1.42  tff(c_435, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_419, c_421])).
% 2.78/1.42  tff(c_438, plain, (![B_92, A_93]: (B_92=A_93 | ~r1_tarski(B_92, A_93) | ~r1_tarski(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.78/1.42  tff(c_443, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_435, c_438])).
% 2.78/1.42  tff(c_456, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_437, c_443])).
% 2.78/1.42  tff(c_467, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_456, c_390])).
% 2.78/1.42  tff(c_575, plain, (![A_106, B_107, C_108, D_109]: (r2_relset_1(A_106, B_107, C_108, C_108) | ~m1_subset_1(D_109, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.78/1.42  tff(c_591, plain, (![A_115, B_116, C_117]: (r2_relset_1(A_115, B_116, C_117, C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(resolution, [status(thm)], [c_467, c_575])).
% 2.78/1.42  tff(c_602, plain, (![A_115, B_116]: (r2_relset_1(A_115, B_116, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_467, c_591])).
% 2.78/1.42  tff(c_457, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_456, c_437])).
% 2.78/1.42  tff(c_418, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_392, c_382, c_44])).
% 2.78/1.42  tff(c_436, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_418, c_421])).
% 2.78/1.42  tff(c_458, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_456, c_436])).
% 2.78/1.42  tff(c_4, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.78/1.42  tff(c_489, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_458, c_4])).
% 2.78/1.42  tff(c_492, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_457, c_489])).
% 2.78/1.42  tff(c_417, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_382, c_32])).
% 2.78/1.42  tff(c_462, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_456, c_456, c_417])).
% 2.78/1.42  tff(c_572, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_492, c_462])).
% 2.78/1.42  tff(c_606, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_602, c_572])).
% 2.78/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.42  
% 2.78/1.42  Inference rules
% 2.78/1.42  ----------------------
% 2.78/1.42  #Ref     : 0
% 2.78/1.42  #Sup     : 118
% 2.78/1.42  #Fact    : 0
% 2.78/1.42  #Define  : 0
% 2.78/1.42  #Split   : 6
% 2.78/1.42  #Chain   : 0
% 2.78/1.42  #Close   : 0
% 2.78/1.42  
% 2.78/1.42  Ordering : KBO
% 2.78/1.43  
% 2.78/1.43  Simplification rules
% 2.78/1.43  ----------------------
% 2.78/1.43  #Subsume      : 11
% 2.78/1.43  #Demod        : 111
% 2.78/1.43  #Tautology    : 73
% 2.78/1.43  #SimpNegUnit  : 2
% 2.78/1.43  #BackRed      : 29
% 2.78/1.43  
% 2.78/1.43  #Partial instantiations: 0
% 2.78/1.43  #Strategies tried      : 1
% 2.78/1.43  
% 2.78/1.43  Timing (in seconds)
% 2.78/1.43  ----------------------
% 2.78/1.43  Preprocessing        : 0.32
% 2.78/1.43  Parsing              : 0.18
% 2.78/1.43  CNF conversion       : 0.02
% 2.78/1.43  Main loop            : 0.29
% 2.78/1.43  Inferencing          : 0.10
% 2.78/1.43  Reduction            : 0.10
% 2.78/1.43  Demodulation         : 0.07
% 2.78/1.43  BG Simplification    : 0.01
% 2.78/1.43  Subsumption          : 0.04
% 2.78/1.43  Abstraction          : 0.01
% 2.78/1.43  MUC search           : 0.00
% 2.78/1.43  Cooper               : 0.00
% 2.78/1.43  Total                : 0.65
% 2.78/1.43  Index Insertion      : 0.00
% 2.78/1.43  Index Deletion       : 0.00
% 2.78/1.43  Index Matching       : 0.00
% 2.78/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
