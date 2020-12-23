%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:20 EST 2020

% Result     : Theorem 4.34s
% Output     : CNFRefutation 4.79s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 284 expanded)
%              Number of leaves         :   40 ( 118 expanded)
%              Depth                    :   11
%              Number of atoms          :  241 (1137 expanded)
%              Number of equality atoms :   98 ( 406 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_178,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
                & v2_funct_1(C) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_136,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_152,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_134,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_124,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_120,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_52,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_145,plain,(
    ! [A_55,B_56,C_57] :
      ( k1_relset_1(A_55,B_56,C_57) = k1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_158,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_145])).

tff(c_254,plain,(
    ! [B_77,A_78,C_79] :
      ( k1_xboole_0 = B_77
      | k1_relset_1(A_78,B_77,C_79) = A_78
      | ~ v1_funct_2(C_79,A_78,B_77)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_263,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_254])).

tff(c_272,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_158,c_263])).

tff(c_273,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_272])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_115,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_124,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_115])).

tff(c_133,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_124])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_121,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_115])).

tff(c_130,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_121])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_72,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_157,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_145])).

tff(c_260,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_254])).

tff(c_268,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_157,c_260])).

tff(c_269,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_268])).

tff(c_46,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_16,plain,(
    ! [A_11,B_13] :
      ( k2_funct_1(A_11) = B_13
      | k6_relat_1(k1_relat_1(A_11)) != k5_relat_1(A_11,B_13)
      | k2_relat_1(A_11) != k1_relat_1(B_13)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_988,plain,(
    ! [A_187,B_188] :
      ( k2_funct_1(A_187) = B_188
      | k6_partfun1(k1_relat_1(A_187)) != k5_relat_1(A_187,B_188)
      | k2_relat_1(A_187) != k1_relat_1(B_188)
      | ~ v2_funct_1(A_187)
      | ~ v1_funct_1(B_188)
      | ~ v1_relat_1(B_188)
      | ~ v1_funct_1(A_187)
      | ~ v1_relat_1(A_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_16])).

tff(c_992,plain,(
    ! [B_188] :
      ( k2_funct_1('#skF_3') = B_188
      | k5_relat_1('#skF_3',B_188) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_188)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_188)
      | ~ v1_relat_1(B_188)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_988])).

tff(c_1007,plain,(
    ! [B_189] :
      ( k2_funct_1('#skF_3') = B_189
      | k5_relat_1('#skF_3',B_189) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_189)
      | ~ v1_funct_1(B_189)
      | ~ v1_relat_1(B_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_74,c_58,c_992])).

tff(c_1013,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_133,c_1007])).

tff(c_1024,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_273,c_1013])).

tff(c_1025,plain,
    ( k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1024])).

tff(c_1030,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1025])).

tff(c_6,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_80,plain,(
    ! [A_6] : k1_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_1139,plain,(
    ! [B_214,C_215,A_216] :
      ( k6_partfun1(B_214) = k5_relat_1(k2_funct_1(C_215),C_215)
      | k1_xboole_0 = B_214
      | ~ v2_funct_1(C_215)
      | k2_relset_1(A_216,B_214,C_215) != B_214
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_216,B_214)))
      | ~ v1_funct_2(C_215,A_216,B_214)
      | ~ v1_funct_1(C_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1143,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1139])).

tff(c_1149,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_62,c_58,c_1143])).

tff(c_1150,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1149])).

tff(c_12,plain,(
    ! [A_10] :
      ( k5_relat_1(k2_funct_1(A_10),A_10) = k6_relat_1(k2_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_77,plain,(
    ! [A_10] :
      ( k5_relat_1(k2_funct_1(A_10),A_10) = k6_partfun1(k2_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_1158,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1150,c_77])).

tff(c_1165,plain,(
    k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_74,c_58,c_1158])).

tff(c_1205,plain,(
    k1_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1165,c_80])).

tff(c_1219,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1205])).

tff(c_1221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1030,c_1219])).

tff(c_1222,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1025])).

tff(c_729,plain,(
    ! [F_149,D_145,A_148,E_147,B_146,C_150] :
      ( k1_partfun1(A_148,B_146,C_150,D_145,E_147,F_149) = k5_relat_1(E_147,F_149)
      | ~ m1_subset_1(F_149,k1_zfmisc_1(k2_zfmisc_1(C_150,D_145)))
      | ~ v1_funct_1(F_149)
      | ~ m1_subset_1(E_147,k1_zfmisc_1(k2_zfmisc_1(A_148,B_146)))
      | ~ v1_funct_1(E_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_735,plain,(
    ! [A_148,B_146,E_147] :
      ( k1_partfun1(A_148,B_146,'#skF_2','#skF_1',E_147,'#skF_4') = k5_relat_1(E_147,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_147,k1_zfmisc_1(k2_zfmisc_1(A_148,B_146)))
      | ~ v1_funct_1(E_147) ) ),
    inference(resolution,[status(thm)],[c_64,c_729])).

tff(c_805,plain,(
    ! [A_162,B_163,E_164] :
      ( k1_partfun1(A_162,B_163,'#skF_2','#skF_1',E_164,'#skF_4') = k5_relat_1(E_164,'#skF_4')
      | ~ m1_subset_1(E_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163)))
      | ~ v1_funct_1(E_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_735])).

tff(c_811,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_805])).

tff(c_818,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_811])).

tff(c_42,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_296,plain,(
    ! [D_80,C_81,A_82,B_83] :
      ( D_80 = C_81
      | ~ r2_relset_1(A_82,B_83,C_81,D_80)
      | ~ m1_subset_1(D_80,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_304,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_296])).

tff(c_319,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_304])).

tff(c_346,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_319])).

tff(c_823,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_818,c_346])).

tff(c_891,plain,(
    ! [F_181,D_183,A_182,B_179,C_178,E_180] :
      ( m1_subset_1(k1_partfun1(A_182,B_179,C_178,D_183,E_180,F_181),k1_zfmisc_1(k2_zfmisc_1(A_182,D_183)))
      | ~ m1_subset_1(F_181,k1_zfmisc_1(k2_zfmisc_1(C_178,D_183)))
      | ~ v1_funct_1(F_181)
      | ~ m1_subset_1(E_180,k1_zfmisc_1(k2_zfmisc_1(A_182,B_179)))
      | ~ v1_funct_1(E_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_945,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_891])).

tff(c_974,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_945])).

tff(c_976,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_823,c_974])).

tff(c_977,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_1314,plain,(
    ! [C_238,B_234,E_235,D_233,F_237,A_236] :
      ( k1_partfun1(A_236,B_234,C_238,D_233,E_235,F_237) = k5_relat_1(E_235,F_237)
      | ~ m1_subset_1(F_237,k1_zfmisc_1(k2_zfmisc_1(C_238,D_233)))
      | ~ v1_funct_1(F_237)
      | ~ m1_subset_1(E_235,k1_zfmisc_1(k2_zfmisc_1(A_236,B_234)))
      | ~ v1_funct_1(E_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1320,plain,(
    ! [A_236,B_234,E_235] :
      ( k1_partfun1(A_236,B_234,'#skF_2','#skF_1',E_235,'#skF_4') = k5_relat_1(E_235,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_235,k1_zfmisc_1(k2_zfmisc_1(A_236,B_234)))
      | ~ v1_funct_1(E_235) ) ),
    inference(resolution,[status(thm)],[c_64,c_1314])).

tff(c_1409,plain,(
    ! [A_246,B_247,E_248] :
      ( k1_partfun1(A_246,B_247,'#skF_2','#skF_1',E_248,'#skF_4') = k5_relat_1(E_248,'#skF_4')
      | ~ m1_subset_1(E_248,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247)))
      | ~ v1_funct_1(E_248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1320])).

tff(c_1415,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1409])).

tff(c_1422,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_977,c_1415])).

tff(c_1424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1222,c_1422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:28:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.34/2.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/2.07  
% 4.70/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/2.07  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.70/2.07  
% 4.70/2.07  %Foreground sorts:
% 4.70/2.07  
% 4.70/2.07  
% 4.70/2.07  %Background operators:
% 4.70/2.07  
% 4.70/2.07  
% 4.70/2.07  %Foreground operators:
% 4.70/2.07  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.70/2.07  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.70/2.07  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.70/2.07  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.70/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.70/2.07  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.70/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.70/2.07  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.70/2.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.70/2.07  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.70/2.07  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.70/2.07  tff('#skF_2', type, '#skF_2': $i).
% 4.70/2.07  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.70/2.07  tff('#skF_3', type, '#skF_3': $i).
% 4.70/2.07  tff('#skF_1', type, '#skF_1': $i).
% 4.70/2.07  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.70/2.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.70/2.07  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.70/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.70/2.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.70/2.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.70/2.07  tff('#skF_4', type, '#skF_4': $i).
% 4.70/2.07  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.70/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.70/2.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.70/2.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.70/2.07  
% 4.79/2.11  tff(f_178, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.79/2.11  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.79/2.11  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.79/2.11  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.79/2.11  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.79/2.11  tff(f_136, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.79/2.11  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 4.79/2.11  tff(f_38, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.79/2.11  tff(f_152, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 4.79/2.11  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 4.79/2.11  tff(f_134, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.79/2.11  tff(f_124, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.79/2.11  tff(f_90, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.79/2.11  tff(f_120, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.79/2.11  tff(c_52, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.79/2.11  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.79/2.11  tff(c_56, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.79/2.11  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.79/2.11  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.79/2.11  tff(c_145, plain, (![A_55, B_56, C_57]: (k1_relset_1(A_55, B_56, C_57)=k1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.79/2.11  tff(c_158, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_145])).
% 4.79/2.11  tff(c_254, plain, (![B_77, A_78, C_79]: (k1_xboole_0=B_77 | k1_relset_1(A_78, B_77, C_79)=A_78 | ~v1_funct_2(C_79, A_78, B_77) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.79/2.11  tff(c_263, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_254])).
% 4.79/2.11  tff(c_272, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_158, c_263])).
% 4.79/2.11  tff(c_273, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_56, c_272])).
% 4.79/2.11  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.79/2.11  tff(c_115, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.79/2.11  tff(c_124, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_64, c_115])).
% 4.79/2.11  tff(c_133, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_124])).
% 4.79/2.11  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.79/2.11  tff(c_121, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_115])).
% 4.79/2.11  tff(c_130, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_121])).
% 4.79/2.11  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.79/2.11  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.79/2.11  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.79/2.11  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.79/2.11  tff(c_157, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_145])).
% 4.79/2.11  tff(c_260, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_254])).
% 4.79/2.11  tff(c_268, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_157, c_260])).
% 4.79/2.11  tff(c_269, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_54, c_268])).
% 4.79/2.11  tff(c_46, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.79/2.11  tff(c_16, plain, (![A_11, B_13]: (k2_funct_1(A_11)=B_13 | k6_relat_1(k1_relat_1(A_11))!=k5_relat_1(A_11, B_13) | k2_relat_1(A_11)!=k1_relat_1(B_13) | ~v2_funct_1(A_11) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.79/2.11  tff(c_988, plain, (![A_187, B_188]: (k2_funct_1(A_187)=B_188 | k6_partfun1(k1_relat_1(A_187))!=k5_relat_1(A_187, B_188) | k2_relat_1(A_187)!=k1_relat_1(B_188) | ~v2_funct_1(A_187) | ~v1_funct_1(B_188) | ~v1_relat_1(B_188) | ~v1_funct_1(A_187) | ~v1_relat_1(A_187))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_16])).
% 4.79/2.11  tff(c_992, plain, (![B_188]: (k2_funct_1('#skF_3')=B_188 | k5_relat_1('#skF_3', B_188)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_188) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_188) | ~v1_relat_1(B_188) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_269, c_988])).
% 4.79/2.11  tff(c_1007, plain, (![B_189]: (k2_funct_1('#skF_3')=B_189 | k5_relat_1('#skF_3', B_189)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_189) | ~v1_funct_1(B_189) | ~v1_relat_1(B_189))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_74, c_58, c_992])).
% 4.79/2.11  tff(c_1013, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_133, c_1007])).
% 4.79/2.11  tff(c_1024, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_273, c_1013])).
% 4.79/2.11  tff(c_1025, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_52, c_1024])).
% 4.79/2.11  tff(c_1030, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_1025])).
% 4.79/2.11  tff(c_6, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.79/2.11  tff(c_80, plain, (![A_6]: (k1_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6])).
% 4.79/2.11  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.79/2.11  tff(c_1139, plain, (![B_214, C_215, A_216]: (k6_partfun1(B_214)=k5_relat_1(k2_funct_1(C_215), C_215) | k1_xboole_0=B_214 | ~v2_funct_1(C_215) | k2_relset_1(A_216, B_214, C_215)!=B_214 | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_216, B_214))) | ~v1_funct_2(C_215, A_216, B_214) | ~v1_funct_1(C_215))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.79/2.11  tff(c_1143, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_1139])).
% 4.79/2.11  tff(c_1149, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_62, c_58, c_1143])).
% 4.79/2.11  tff(c_1150, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_1149])).
% 4.79/2.11  tff(c_12, plain, (![A_10]: (k5_relat_1(k2_funct_1(A_10), A_10)=k6_relat_1(k2_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.79/2.11  tff(c_77, plain, (![A_10]: (k5_relat_1(k2_funct_1(A_10), A_10)=k6_partfun1(k2_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 4.79/2.11  tff(c_1158, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1150, c_77])).
% 4.79/2.11  tff(c_1165, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_74, c_58, c_1158])).
% 4.79/2.11  tff(c_1205, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1165, c_80])).
% 4.79/2.11  tff(c_1219, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1205])).
% 4.79/2.11  tff(c_1221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1030, c_1219])).
% 4.79/2.11  tff(c_1222, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1025])).
% 4.79/2.11  tff(c_729, plain, (![F_149, D_145, A_148, E_147, B_146, C_150]: (k1_partfun1(A_148, B_146, C_150, D_145, E_147, F_149)=k5_relat_1(E_147, F_149) | ~m1_subset_1(F_149, k1_zfmisc_1(k2_zfmisc_1(C_150, D_145))) | ~v1_funct_1(F_149) | ~m1_subset_1(E_147, k1_zfmisc_1(k2_zfmisc_1(A_148, B_146))) | ~v1_funct_1(E_147))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.79/2.11  tff(c_735, plain, (![A_148, B_146, E_147]: (k1_partfun1(A_148, B_146, '#skF_2', '#skF_1', E_147, '#skF_4')=k5_relat_1(E_147, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_147, k1_zfmisc_1(k2_zfmisc_1(A_148, B_146))) | ~v1_funct_1(E_147))), inference(resolution, [status(thm)], [c_64, c_729])).
% 4.79/2.11  tff(c_805, plain, (![A_162, B_163, E_164]: (k1_partfun1(A_162, B_163, '#skF_2', '#skF_1', E_164, '#skF_4')=k5_relat_1(E_164, '#skF_4') | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))) | ~v1_funct_1(E_164))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_735])).
% 4.79/2.11  tff(c_811, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_805])).
% 4.79/2.11  tff(c_818, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_811])).
% 4.79/2.11  tff(c_42, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.79/2.11  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.79/2.11  tff(c_296, plain, (![D_80, C_81, A_82, B_83]: (D_80=C_81 | ~r2_relset_1(A_82, B_83, C_81, D_80) | ~m1_subset_1(D_80, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.79/2.11  tff(c_304, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_296])).
% 4.79/2.11  tff(c_319, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_304])).
% 4.79/2.11  tff(c_346, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_319])).
% 4.79/2.11  tff(c_823, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_818, c_346])).
% 4.79/2.11  tff(c_891, plain, (![F_181, D_183, A_182, B_179, C_178, E_180]: (m1_subset_1(k1_partfun1(A_182, B_179, C_178, D_183, E_180, F_181), k1_zfmisc_1(k2_zfmisc_1(A_182, D_183))) | ~m1_subset_1(F_181, k1_zfmisc_1(k2_zfmisc_1(C_178, D_183))) | ~v1_funct_1(F_181) | ~m1_subset_1(E_180, k1_zfmisc_1(k2_zfmisc_1(A_182, B_179))) | ~v1_funct_1(E_180))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.79/2.11  tff(c_945, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_818, c_891])).
% 4.79/2.11  tff(c_974, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_945])).
% 4.79/2.11  tff(c_976, plain, $false, inference(negUnitSimplification, [status(thm)], [c_823, c_974])).
% 4.79/2.11  tff(c_977, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_319])).
% 4.79/2.11  tff(c_1314, plain, (![C_238, B_234, E_235, D_233, F_237, A_236]: (k1_partfun1(A_236, B_234, C_238, D_233, E_235, F_237)=k5_relat_1(E_235, F_237) | ~m1_subset_1(F_237, k1_zfmisc_1(k2_zfmisc_1(C_238, D_233))) | ~v1_funct_1(F_237) | ~m1_subset_1(E_235, k1_zfmisc_1(k2_zfmisc_1(A_236, B_234))) | ~v1_funct_1(E_235))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.79/2.11  tff(c_1320, plain, (![A_236, B_234, E_235]: (k1_partfun1(A_236, B_234, '#skF_2', '#skF_1', E_235, '#skF_4')=k5_relat_1(E_235, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_235, k1_zfmisc_1(k2_zfmisc_1(A_236, B_234))) | ~v1_funct_1(E_235))), inference(resolution, [status(thm)], [c_64, c_1314])).
% 4.79/2.11  tff(c_1409, plain, (![A_246, B_247, E_248]: (k1_partfun1(A_246, B_247, '#skF_2', '#skF_1', E_248, '#skF_4')=k5_relat_1(E_248, '#skF_4') | ~m1_subset_1(E_248, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))) | ~v1_funct_1(E_248))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1320])).
% 4.79/2.11  tff(c_1415, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_1409])).
% 4.79/2.11  tff(c_1422, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_977, c_1415])).
% 4.79/2.11  tff(c_1424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1222, c_1422])).
% 4.79/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.79/2.11  
% 4.79/2.11  Inference rules
% 4.79/2.11  ----------------------
% 4.79/2.11  #Ref     : 0
% 4.79/2.11  #Sup     : 296
% 4.79/2.11  #Fact    : 0
% 4.79/2.11  #Define  : 0
% 4.79/2.11  #Split   : 11
% 4.79/2.11  #Chain   : 0
% 4.79/2.11  #Close   : 0
% 4.79/2.11  
% 4.79/2.11  Ordering : KBO
% 4.79/2.11  
% 4.79/2.11  Simplification rules
% 4.79/2.11  ----------------------
% 4.79/2.11  #Subsume      : 17
% 4.79/2.11  #Demod        : 296
% 4.79/2.11  #Tautology    : 103
% 4.79/2.11  #SimpNegUnit  : 25
% 4.79/2.11  #BackRed      : 18
% 4.79/2.11  
% 4.79/2.11  #Partial instantiations: 0
% 4.79/2.11  #Strategies tried      : 1
% 4.79/2.11  
% 4.79/2.11  Timing (in seconds)
% 4.79/2.11  ----------------------
% 4.79/2.11  Preprocessing        : 0.57
% 4.79/2.11  Parsing              : 0.30
% 4.79/2.11  CNF conversion       : 0.04
% 4.79/2.11  Main loop            : 0.68
% 4.79/2.11  Inferencing          : 0.24
% 4.79/2.11  Reduction            : 0.23
% 4.79/2.11  Demodulation         : 0.17
% 4.79/2.11  BG Simplification    : 0.04
% 4.79/2.11  Subsumption          : 0.12
% 4.79/2.11  Abstraction          : 0.03
% 4.79/2.12  MUC search           : 0.00
% 4.79/2.12  Cooper               : 0.00
% 4.79/2.12  Total                : 1.32
% 4.79/2.12  Index Insertion      : 0.00
% 4.79/2.12  Index Deletion       : 0.00
% 4.79/2.12  Index Matching       : 0.00
% 4.79/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
