%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:29 EST 2020

% Result     : Theorem 15.34s
% Output     : CNFRefutation 15.34s
% Verified   : 
% Statistics : Number of formulae       :  207 (31928 expanded)
%              Number of leaves         :   62 (10628 expanded)
%              Depth                    :   29
%              Number of atoms          :  464 (89819 expanded)
%              Number of equality atoms :  133 (20319 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_345,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => r2_funct_2(u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_303,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_159,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_165,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_211,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_169,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_257,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_224,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_240,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_273,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_226,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_289,axiom,(
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

tff(f_128,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_138,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_155,axiom,(
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

tff(f_299,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_323,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_311,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_138,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_345])).

tff(c_194,plain,(
    ! [A_96] :
      ( u1_struct_0(A_96) = k2_struct_0(A_96)
      | ~ l1_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_202,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_138,c_194])).

tff(c_134,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_345])).

tff(c_201,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_134,c_194])).

tff(c_128,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_345])).

tff(c_203,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_128])).

tff(c_362,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_203])).

tff(c_58,plain,(
    ! [C_33,A_31,B_32] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_372,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_362,c_58])).

tff(c_132,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_345])).

tff(c_16,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1044,plain,(
    ! [C_184,A_185,B_186] :
      ( v4_relat_1(C_184,A_185)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1057,plain,(
    v4_relat_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_362,c_1044])).

tff(c_1141,plain,(
    ! [B_197,A_198] :
      ( k1_relat_1(B_197) = A_198
      | ~ v1_partfun1(B_197,A_198)
      | ~ v4_relat_1(B_197,A_198)
      | ~ v1_relat_1(B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_1144,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1057,c_1141])).

tff(c_1153,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_1144])).

tff(c_1166,plain,(
    ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1153])).

tff(c_386,plain,(
    ! [A_121] :
      ( k2_relat_1(A_121) = k1_xboole_0
      | k1_relat_1(A_121) != k1_xboole_0
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_405,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_372,c_386])).

tff(c_954,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_956,plain,(
    ! [A_171] :
      ( k1_relat_1(A_171) = k1_xboole_0
      | k2_relat_1(A_171) != k1_xboole_0
      | ~ v1_relat_1(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_959,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_372,c_956])).

tff(c_977,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_954,c_959])).

tff(c_1246,plain,(
    ! [A_208,B_209,C_210] :
      ( k2_relset_1(A_208,B_209,C_210) = k2_relat_1(C_210)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1259,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_362,c_1246])).

tff(c_126,plain,(
    k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_345])).

tff(c_224,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_201,c_126])).

tff(c_1377,plain,(
    k2_struct_0('#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1259,c_224])).

tff(c_130,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_345])).

tff(c_204,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_130])).

tff(c_223,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_204])).

tff(c_1388,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1377,c_223])).

tff(c_1385,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1377,c_362])).

tff(c_1531,plain,(
    ! [B_227,C_228,A_229] :
      ( k1_xboole_0 = B_227
      | v1_partfun1(C_228,A_229)
      | ~ v1_funct_2(C_228,A_229,B_227)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_229,B_227)))
      | ~ v1_funct_1(C_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_1534,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1385,c_1531])).

tff(c_1549,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1388,c_1534])).

tff(c_1551,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1166,c_977,c_1549])).

tff(c_1552,plain,(
    k2_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1153])).

tff(c_1556,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1552,c_362])).

tff(c_1751,plain,(
    ! [A_239,B_240,C_241] :
      ( k2_relset_1(A_239,B_240,C_241) = k2_relat_1(C_241)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1768,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1556,c_1751])).

tff(c_1559,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1552,c_224])).

tff(c_1828,plain,(
    k2_struct_0('#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1768,c_1559])).

tff(c_1560,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1552,c_223])).

tff(c_1837,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1828,c_1560])).

tff(c_1835,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1828,c_1556])).

tff(c_82,plain,(
    ! [A_50,B_51] : v1_funct_1('#skF_1'(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_80,plain,(
    ! [A_50,B_51] : v1_funct_2('#skF_1'(A_50,B_51),A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_90,plain,(
    ! [A_50,B_51] : m1_subset_1('#skF_1'(A_50,B_51),k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_5922,plain,(
    ! [A_398,B_399,C_400,D_401] :
      ( r2_funct_2(A_398,B_399,C_400,C_400)
      | ~ m1_subset_1(D_401,k1_zfmisc_1(k2_zfmisc_1(A_398,B_399)))
      | ~ v1_funct_2(D_401,A_398,B_399)
      | ~ v1_funct_1(D_401)
      | ~ m1_subset_1(C_400,k1_zfmisc_1(k2_zfmisc_1(A_398,B_399)))
      | ~ v1_funct_2(C_400,A_398,B_399)
      | ~ v1_funct_1(C_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_5936,plain,(
    ! [A_50,B_51,C_400] :
      ( r2_funct_2(A_50,B_51,C_400,C_400)
      | ~ v1_funct_2('#skF_1'(A_50,B_51),A_50,B_51)
      | ~ v1_funct_1('#skF_1'(A_50,B_51))
      | ~ m1_subset_1(C_400,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | ~ v1_funct_2(C_400,A_50,B_51)
      | ~ v1_funct_1(C_400) ) ),
    inference(resolution,[status(thm)],[c_90,c_5922])).

tff(c_9823,plain,(
    ! [A_529,B_530,C_531] :
      ( r2_funct_2(A_529,B_530,C_531,C_531)
      | ~ m1_subset_1(C_531,k1_zfmisc_1(k2_zfmisc_1(A_529,B_530)))
      | ~ v1_funct_2(C_531,A_529,B_530)
      | ~ v1_funct_1(C_531) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_5936])).

tff(c_9839,plain,
    ( r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1835,c_9823])).

tff(c_9869,plain,(
    r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1837,c_9839])).

tff(c_124,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_345])).

tff(c_34,plain,(
    ! [A_18] :
      ( v1_relat_1(k2_funct_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1833,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1828,c_1768])).

tff(c_3320,plain,(
    ! [C_311,A_312,B_313] :
      ( v1_funct_1(k2_funct_1(C_311))
      | k2_relset_1(A_312,B_313,C_311) != B_313
      | ~ v2_funct_1(C_311)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(A_312,B_313)))
      | ~ v1_funct_2(C_311,A_312,B_313)
      | ~ v1_funct_1(C_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_3323,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1835,c_3320])).

tff(c_3338,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1837,c_124,c_1833,c_3323])).

tff(c_92,plain,(
    ! [A_53] : k6_relat_1(A_53) = k6_partfun1(A_53) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_38,plain,(
    ! [A_19] : v2_funct_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_140,plain,(
    ! [A_19] : v2_funct_1(k6_partfun1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_38])).

tff(c_5066,plain,(
    ! [A_372,C_373,B_374] :
      ( k6_partfun1(A_372) = k5_relat_1(C_373,k2_funct_1(C_373))
      | k1_xboole_0 = B_374
      | ~ v2_funct_1(C_373)
      | k2_relset_1(A_372,B_374,C_373) != B_374
      | ~ m1_subset_1(C_373,k1_zfmisc_1(k2_zfmisc_1(A_372,B_374)))
      | ~ v1_funct_2(C_373,A_372,B_374)
      | ~ v1_funct_1(C_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_5074,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1(k1_relat_1('#skF_4'))
    | k2_relat_1('#skF_4') = k1_xboole_0
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1835,c_5066])).

tff(c_5094,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1(k1_relat_1('#skF_4'))
    | k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1837,c_1833,c_124,c_5074])).

tff(c_5095,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1(k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_977,c_5094])).

tff(c_48,plain,(
    ! [A_24,B_26] :
      ( v2_funct_1(A_24)
      | k2_relat_1(B_26) != k1_relat_1(A_24)
      | ~ v2_funct_1(k5_relat_1(B_26,A_24))
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_5109,plain,
    ( v2_funct_1(k2_funct_1('#skF_4'))
    | k1_relat_1(k2_funct_1('#skF_4')) != k2_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1(k1_relat_1('#skF_4')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5095,c_48])).

tff(c_5119,plain,
    ( v2_funct_1(k2_funct_1('#skF_4'))
    | k1_relat_1(k2_funct_1('#skF_4')) != k2_relat_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3338,c_372,c_132,c_140,c_5109])).

tff(c_12136,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5119])).

tff(c_12143,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_12136])).

tff(c_12147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_132,c_12143])).

tff(c_12149,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5119])).

tff(c_54,plain,(
    ! [A_27] :
      ( k1_relat_1(k2_funct_1(A_27)) = k2_relat_1(A_27)
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_12148,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != k2_relat_1('#skF_4')
    | v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5119])).

tff(c_12158,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != k2_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_12148])).

tff(c_12196,plain,
    ( ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_12158])).

tff(c_12200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_132,c_124,c_12196])).

tff(c_12201,plain,(
    v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_12148])).

tff(c_12202,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_12148])).

tff(c_24,plain,(
    ! [A_15] :
      ( k9_relat_1(A_15,k1_relat_1(A_15)) = k2_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12244,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4')) = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12202,c_24])).

tff(c_12279,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4')) = k2_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12149,c_12244])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2173,plain,(
    ! [A_273,B_274] :
      ( k9_relat_1(k2_funct_1(A_273),k9_relat_1(A_273,B_274)) = B_274
      | ~ r1_tarski(B_274,k1_relat_1(A_273))
      | ~ v2_funct_1(A_273)
      | ~ v1_funct_1(A_273)
      | ~ v1_relat_1(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2191,plain,(
    ! [A_15] :
      ( k9_relat_1(k2_funct_1(A_15),k2_relat_1(A_15)) = k1_relat_1(A_15)
      | ~ r1_tarski(k1_relat_1(A_15),k1_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2173])).

tff(c_2197,plain,(
    ! [A_15] :
      ( k9_relat_1(k2_funct_1(A_15),k2_relat_1(A_15)) = k1_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2191])).

tff(c_12318,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12279,c_2197])).

tff(c_12334,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_132,c_124,c_12318])).

tff(c_5558,plain,(
    ! [B_387,C_388,A_389] :
      ( k6_partfun1(B_387) = k5_relat_1(k2_funct_1(C_388),C_388)
      | k1_xboole_0 = B_387
      | ~ v2_funct_1(C_388)
      | k2_relset_1(A_389,B_387,C_388) != B_387
      | ~ m1_subset_1(C_388,k1_zfmisc_1(k2_zfmisc_1(A_389,B_387)))
      | ~ v1_funct_2(C_388,A_389,B_387)
      | ~ v1_funct_1(C_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_5566,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1(k2_relat_1('#skF_4'))
    | k2_relat_1('#skF_4') = k1_xboole_0
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1835,c_5558])).

tff(c_5586,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1(k2_relat_1('#skF_4'))
    | k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1837,c_1833,c_124,c_5566])).

tff(c_5587,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1(k2_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_977,c_5586])).

tff(c_56,plain,(
    ! [A_28,B_30] :
      ( k2_funct_1(A_28) = B_30
      | k6_relat_1(k1_relat_1(A_28)) != k5_relat_1(A_28,B_30)
      | k2_relat_1(A_28) != k1_relat_1(B_30)
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_3362,plain,(
    ! [A_319,B_320] :
      ( k2_funct_1(A_319) = B_320
      | k6_partfun1(k1_relat_1(A_319)) != k5_relat_1(A_319,B_320)
      | k2_relat_1(A_319) != k1_relat_1(B_320)
      | ~ v2_funct_1(A_319)
      | ~ v1_funct_1(B_320)
      | ~ v1_relat_1(B_320)
      | ~ v1_funct_1(A_319)
      | ~ v1_relat_1(A_319) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_56])).

tff(c_32484,plain,(
    ! [A_893,B_894] :
      ( k2_funct_1(k2_funct_1(A_893)) = B_894
      | k5_relat_1(k2_funct_1(A_893),B_894) != k6_partfun1(k2_relat_1(A_893))
      | k2_relat_1(k2_funct_1(A_893)) != k1_relat_1(B_894)
      | ~ v2_funct_1(k2_funct_1(A_893))
      | ~ v1_funct_1(B_894)
      | ~ v1_relat_1(B_894)
      | ~ v1_funct_1(k2_funct_1(A_893))
      | ~ v1_relat_1(k2_funct_1(A_893))
      | ~ v2_funct_1(A_893)
      | ~ v1_funct_1(A_893)
      | ~ v1_relat_1(A_893) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_3362])).

tff(c_32492,plain,
    ( k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4'
    | k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5587,c_32484])).

tff(c_32503,plain,(
    k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_132,c_124,c_12149,c_3338,c_12201,c_12334,c_32492])).

tff(c_3770,plain,(
    ! [C_331,B_332,A_333] :
      ( v1_funct_2(k2_funct_1(C_331),B_332,A_333)
      | k2_relset_1(A_333,B_332,C_331) != B_332
      | ~ v2_funct_1(C_331)
      | ~ m1_subset_1(C_331,k1_zfmisc_1(k2_zfmisc_1(A_333,B_332)))
      | ~ v1_funct_2(C_331,A_333,B_332)
      | ~ v1_funct_1(C_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_3773,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1835,c_3770])).

tff(c_3788,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1837,c_124,c_1833,c_3773])).

tff(c_110,plain,(
    ! [A_67] :
      ( m1_subset_1(A_67,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_67),k2_relat_1(A_67))))
      | ~ v1_funct_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_1767,plain,(
    ! [A_67] :
      ( k2_relset_1(k1_relat_1(A_67),k2_relat_1(A_67),A_67) = k2_relat_1(A_67)
      | ~ v1_funct_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(resolution,[status(thm)],[c_110,c_1751])).

tff(c_12372,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12334,c_1767])).

tff(c_12415,plain,(
    k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12149,c_3338,c_12334,c_12202,c_12372])).

tff(c_4107,plain,(
    ! [A_342,B_343,C_344] :
      ( k2_tops_2(A_342,B_343,C_344) = k2_funct_1(C_344)
      | ~ v2_funct_1(C_344)
      | k2_relset_1(A_342,B_343,C_344) != B_343
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(A_342,B_343)))
      | ~ v1_funct_2(C_344,A_342,B_343)
      | ~ v1_funct_1(C_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_26315,plain,(
    ! [A_805] :
      ( k2_tops_2(k1_relat_1(A_805),k2_relat_1(A_805),A_805) = k2_funct_1(A_805)
      | ~ v2_funct_1(A_805)
      | k2_relset_1(k1_relat_1(A_805),k2_relat_1(A_805),A_805) != k2_relat_1(A_805)
      | ~ v1_funct_2(A_805,k1_relat_1(A_805),k2_relat_1(A_805))
      | ~ v1_funct_1(A_805)
      | ~ v1_relat_1(A_805) ) ),
    inference(resolution,[status(thm)],[c_110,c_4107])).

tff(c_26351,plain,
    ( k2_tops_2(k1_relat_1(k2_funct_1('#skF_4')),k2_relat_1(k2_funct_1('#skF_4')),k2_funct_1('#skF_4')) = k2_funct_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1(k1_relat_1(k2_funct_1('#skF_4')),k2_relat_1(k2_funct_1('#skF_4')),k2_funct_1('#skF_4')) != k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12334,c_26315])).

tff(c_26465,plain,(
    k2_tops_2(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k2_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12149,c_3338,c_3788,c_12202,c_12415,c_12334,c_12334,c_12202,c_12201,c_12334,c_12202,c_26351])).

tff(c_4113,plain,
    ( k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_funct_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1835,c_4107])).

tff(c_4131,plain,(
    k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1837,c_1833,c_124,c_4113])).

tff(c_122,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_345])).

tff(c_265,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_202,c_202,c_201,c_201,c_201,c_122])).

tff(c_1557,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k1_relat_1('#skF_4'),k2_tops_2(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1552,c_1552,c_1552,c_265])).

tff(c_1834,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),k2_tops_2(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1828,c_1828,c_1828,c_1557])).

tff(c_4136,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),k2_tops_2(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4131,c_1834])).

tff(c_26521,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26465,c_4136])).

tff(c_32524,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32503,c_26521])).

tff(c_32539,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9869,c_32524])).

tff(c_32541,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_32861,plain,(
    ! [A_931] :
      ( m1_subset_1(A_931,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_931),k2_relat_1(A_931))))
      | ~ v1_funct_1(A_931)
      | ~ v1_relat_1(A_931) ) ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_32894,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4'))))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_32541,c_32861])).

tff(c_32918,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_132,c_16,c_32894])).

tff(c_18,plain,(
    ! [B_9,A_7] :
      ( v1_xboole_0(B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_7))
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32954,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32918,c_18])).

tff(c_32964,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32954])).

tff(c_209,plain,(
    ! [B_97,A_98] :
      ( ~ v1_xboole_0(B_97)
      | B_97 = A_98
      | ~ v1_xboole_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_212,plain,(
    ! [A_98] :
      ( k1_xboole_0 = A_98
      | ~ v1_xboole_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_2,c_209])).

tff(c_32976,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32964,c_212])).

tff(c_32540,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_32925,plain,(
    ! [A_932,B_933,C_934] :
      ( k2_relset_1(A_932,B_933,C_934) = k2_relat_1(C_934)
      | ~ m1_subset_1(C_934,k1_zfmisc_1(k2_zfmisc_1(A_932,B_933))) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_32931,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_362,c_32925])).

tff(c_32943,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32540,c_32931])).

tff(c_33023,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32976,c_32943])).

tff(c_33024,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33023,c_224])).

tff(c_136,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_345])).

tff(c_231,plain,(
    ! [A_102] :
      ( ~ v1_xboole_0(u1_struct_0(A_102))
      | ~ l1_struct_0(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_237,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_231])).

tff(c_241,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_237])).

tff(c_242,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_241])).

tff(c_33098,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33024,c_242])).

tff(c_33103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32964,c_33098])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:31:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.34/7.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.34/7.65  
% 15.34/7.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.34/7.65  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 15.34/7.65  
% 15.34/7.65  %Foreground sorts:
% 15.34/7.65  
% 15.34/7.65  
% 15.34/7.65  %Background operators:
% 15.34/7.65  
% 15.34/7.65  
% 15.34/7.65  %Foreground operators:
% 15.34/7.65  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 15.34/7.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 15.34/7.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.34/7.65  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 15.34/7.65  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 15.34/7.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.34/7.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.34/7.65  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 15.34/7.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.34/7.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.34/7.65  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 15.34/7.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 15.34/7.65  tff('#skF_2', type, '#skF_2': $i).
% 15.34/7.65  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 15.34/7.65  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 15.34/7.65  tff('#skF_3', type, '#skF_3': $i).
% 15.34/7.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 15.34/7.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.34/7.65  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 15.34/7.65  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 15.34/7.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.34/7.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.34/7.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.34/7.65  tff('#skF_4', type, '#skF_4': $i).
% 15.34/7.65  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 15.34/7.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.34/7.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 15.34/7.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.34/7.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.34/7.65  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 15.34/7.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.34/7.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.34/7.65  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 15.34/7.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.34/7.65  
% 15.34/7.68  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 15.34/7.68  tff(f_345, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 15.34/7.68  tff(f_303, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 15.34/7.68  tff(f_159, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 15.34/7.68  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 15.34/7.68  tff(f_165, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 15.34/7.68  tff(f_211, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 15.34/7.68  tff(f_72, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 15.34/7.68  tff(f_169, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 15.34/7.68  tff(f_257, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 15.34/7.68  tff(f_224, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 15.34/7.68  tff(f_240, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 15.34/7.68  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 15.34/7.68  tff(f_273, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 15.34/7.68  tff(f_226, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 15.34/7.68  tff(f_88, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 15.34/7.68  tff(f_289, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 15.34/7.68  tff(f_128, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 15.34/7.68  tff(f_138, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 15.34/7.68  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 15.34/7.68  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.34/7.68  tff(f_111, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 15.34/7.68  tff(f_155, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 15.34/7.68  tff(f_299, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 15.34/7.68  tff(f_323, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 15.34/7.68  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 15.34/7.68  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 15.34/7.68  tff(f_311, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 15.34/7.68  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 15.34/7.68  tff(c_138, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_345])).
% 15.34/7.68  tff(c_194, plain, (![A_96]: (u1_struct_0(A_96)=k2_struct_0(A_96) | ~l1_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_303])).
% 15.34/7.68  tff(c_202, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_138, c_194])).
% 15.34/7.68  tff(c_134, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_345])).
% 15.34/7.68  tff(c_201, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_134, c_194])).
% 15.34/7.68  tff(c_128, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_345])).
% 15.34/7.68  tff(c_203, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_128])).
% 15.34/7.68  tff(c_362, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_203])).
% 15.34/7.68  tff(c_58, plain, (![C_33, A_31, B_32]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_159])).
% 15.34/7.68  tff(c_372, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_362, c_58])).
% 15.34/7.68  tff(c_132, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_345])).
% 15.34/7.68  tff(c_16, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 15.34/7.68  tff(c_1044, plain, (![C_184, A_185, B_186]: (v4_relat_1(C_184, A_185) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_165])).
% 15.34/7.68  tff(c_1057, plain, (v4_relat_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_362, c_1044])).
% 15.34/7.68  tff(c_1141, plain, (![B_197, A_198]: (k1_relat_1(B_197)=A_198 | ~v1_partfun1(B_197, A_198) | ~v4_relat_1(B_197, A_198) | ~v1_relat_1(B_197))), inference(cnfTransformation, [status(thm)], [f_211])).
% 15.34/7.68  tff(c_1144, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1057, c_1141])).
% 15.34/7.68  tff(c_1153, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_372, c_1144])).
% 15.34/7.68  tff(c_1166, plain, (~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1153])).
% 15.34/7.68  tff(c_386, plain, (![A_121]: (k2_relat_1(A_121)=k1_xboole_0 | k1_relat_1(A_121)!=k1_xboole_0 | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.34/7.68  tff(c_405, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_372, c_386])).
% 15.34/7.68  tff(c_954, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_405])).
% 15.34/7.68  tff(c_956, plain, (![A_171]: (k1_relat_1(A_171)=k1_xboole_0 | k2_relat_1(A_171)!=k1_xboole_0 | ~v1_relat_1(A_171))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.34/7.68  tff(c_959, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_372, c_956])).
% 15.34/7.68  tff(c_977, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_954, c_959])).
% 15.34/7.68  tff(c_1246, plain, (![A_208, B_209, C_210]: (k2_relset_1(A_208, B_209, C_210)=k2_relat_1(C_210) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))))), inference(cnfTransformation, [status(thm)], [f_169])).
% 15.34/7.68  tff(c_1259, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_362, c_1246])).
% 15.34/7.68  tff(c_126, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_345])).
% 15.34/7.68  tff(c_224, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_202, c_201, c_126])).
% 15.34/7.68  tff(c_1377, plain, (k2_struct_0('#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1259, c_224])).
% 15.34/7.68  tff(c_130, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_345])).
% 15.34/7.68  tff(c_204, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_130])).
% 15.34/7.68  tff(c_223, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_204])).
% 15.34/7.68  tff(c_1388, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1377, c_223])).
% 15.34/7.68  tff(c_1385, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_1377, c_362])).
% 15.34/7.68  tff(c_1531, plain, (![B_227, C_228, A_229]: (k1_xboole_0=B_227 | v1_partfun1(C_228, A_229) | ~v1_funct_2(C_228, A_229, B_227) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_229, B_227))) | ~v1_funct_1(C_228))), inference(cnfTransformation, [status(thm)], [f_257])).
% 15.34/7.68  tff(c_1534, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1385, c_1531])).
% 15.34/7.68  tff(c_1549, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_1388, c_1534])).
% 15.34/7.68  tff(c_1551, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1166, c_977, c_1549])).
% 15.34/7.68  tff(c_1552, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_1153])).
% 15.34/7.68  tff(c_1556, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1552, c_362])).
% 15.34/7.68  tff(c_1751, plain, (![A_239, B_240, C_241]: (k2_relset_1(A_239, B_240, C_241)=k2_relat_1(C_241) | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))))), inference(cnfTransformation, [status(thm)], [f_169])).
% 15.34/7.68  tff(c_1768, plain, (k2_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1556, c_1751])).
% 15.34/7.68  tff(c_1559, plain, (k2_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1552, c_224])).
% 15.34/7.68  tff(c_1828, plain, (k2_struct_0('#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1768, c_1559])).
% 15.34/7.68  tff(c_1560, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1552, c_223])).
% 15.34/7.68  tff(c_1837, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1828, c_1560])).
% 15.34/7.68  tff(c_1835, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_1828, c_1556])).
% 15.34/7.68  tff(c_82, plain, (![A_50, B_51]: (v1_funct_1('#skF_1'(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_224])).
% 15.34/7.68  tff(c_80, plain, (![A_50, B_51]: (v1_funct_2('#skF_1'(A_50, B_51), A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_224])).
% 15.34/7.68  tff(c_90, plain, (![A_50, B_51]: (m1_subset_1('#skF_1'(A_50, B_51), k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_224])).
% 15.34/7.68  tff(c_5922, plain, (![A_398, B_399, C_400, D_401]: (r2_funct_2(A_398, B_399, C_400, C_400) | ~m1_subset_1(D_401, k1_zfmisc_1(k2_zfmisc_1(A_398, B_399))) | ~v1_funct_2(D_401, A_398, B_399) | ~v1_funct_1(D_401) | ~m1_subset_1(C_400, k1_zfmisc_1(k2_zfmisc_1(A_398, B_399))) | ~v1_funct_2(C_400, A_398, B_399) | ~v1_funct_1(C_400))), inference(cnfTransformation, [status(thm)], [f_240])).
% 15.34/7.68  tff(c_5936, plain, (![A_50, B_51, C_400]: (r2_funct_2(A_50, B_51, C_400, C_400) | ~v1_funct_2('#skF_1'(A_50, B_51), A_50, B_51) | ~v1_funct_1('#skF_1'(A_50, B_51)) | ~m1_subset_1(C_400, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))) | ~v1_funct_2(C_400, A_50, B_51) | ~v1_funct_1(C_400))), inference(resolution, [status(thm)], [c_90, c_5922])).
% 15.34/7.68  tff(c_9823, plain, (![A_529, B_530, C_531]: (r2_funct_2(A_529, B_530, C_531, C_531) | ~m1_subset_1(C_531, k1_zfmisc_1(k2_zfmisc_1(A_529, B_530))) | ~v1_funct_2(C_531, A_529, B_530) | ~v1_funct_1(C_531))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_5936])).
% 15.34/7.68  tff(c_9839, plain, (r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1835, c_9823])).
% 15.34/7.68  tff(c_9869, plain, (r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_1837, c_9839])).
% 15.34/7.68  tff(c_124, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_345])).
% 15.34/7.68  tff(c_34, plain, (![A_18]: (v1_relat_1(k2_funct_1(A_18)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_84])).
% 15.34/7.68  tff(c_1833, plain, (k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1828, c_1768])).
% 15.34/7.68  tff(c_3320, plain, (![C_311, A_312, B_313]: (v1_funct_1(k2_funct_1(C_311)) | k2_relset_1(A_312, B_313, C_311)!=B_313 | ~v2_funct_1(C_311) | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1(A_312, B_313))) | ~v1_funct_2(C_311, A_312, B_313) | ~v1_funct_1(C_311))), inference(cnfTransformation, [status(thm)], [f_273])).
% 15.34/7.68  tff(c_3323, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1835, c_3320])).
% 15.34/7.68  tff(c_3338, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_1837, c_124, c_1833, c_3323])).
% 15.34/7.68  tff(c_92, plain, (![A_53]: (k6_relat_1(A_53)=k6_partfun1(A_53))), inference(cnfTransformation, [status(thm)], [f_226])).
% 15.34/7.68  tff(c_38, plain, (![A_19]: (v2_funct_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 15.34/7.68  tff(c_140, plain, (![A_19]: (v2_funct_1(k6_partfun1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_38])).
% 15.34/7.68  tff(c_5066, plain, (![A_372, C_373, B_374]: (k6_partfun1(A_372)=k5_relat_1(C_373, k2_funct_1(C_373)) | k1_xboole_0=B_374 | ~v2_funct_1(C_373) | k2_relset_1(A_372, B_374, C_373)!=B_374 | ~m1_subset_1(C_373, k1_zfmisc_1(k2_zfmisc_1(A_372, B_374))) | ~v1_funct_2(C_373, A_372, B_374) | ~v1_funct_1(C_373))), inference(cnfTransformation, [status(thm)], [f_289])).
% 15.34/7.68  tff(c_5074, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1(k1_relat_1('#skF_4')) | k2_relat_1('#skF_4')=k1_xboole_0 | ~v2_funct_1('#skF_4') | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1835, c_5066])).
% 15.34/7.68  tff(c_5094, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1(k1_relat_1('#skF_4')) | k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_132, c_1837, c_1833, c_124, c_5074])).
% 15.34/7.68  tff(c_5095, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1(k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_977, c_5094])).
% 15.34/7.68  tff(c_48, plain, (![A_24, B_26]: (v2_funct_1(A_24) | k2_relat_1(B_26)!=k1_relat_1(A_24) | ~v2_funct_1(k5_relat_1(B_26, A_24)) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_128])).
% 15.34/7.68  tff(c_5109, plain, (v2_funct_1(k2_funct_1('#skF_4')) | k1_relat_1(k2_funct_1('#skF_4'))!=k2_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1(k1_relat_1('#skF_4'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5095, c_48])).
% 15.34/7.68  tff(c_5119, plain, (v2_funct_1(k2_funct_1('#skF_4')) | k1_relat_1(k2_funct_1('#skF_4'))!=k2_relat_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3338, c_372, c_132, c_140, c_5109])).
% 15.34/7.68  tff(c_12136, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5119])).
% 15.34/7.68  tff(c_12143, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_12136])).
% 15.34/7.68  tff(c_12147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_372, c_132, c_12143])).
% 15.34/7.68  tff(c_12149, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_5119])).
% 15.34/7.68  tff(c_54, plain, (![A_27]: (k1_relat_1(k2_funct_1(A_27))=k2_relat_1(A_27) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_138])).
% 15.34/7.68  tff(c_12148, plain, (k1_relat_1(k2_funct_1('#skF_4'))!=k2_relat_1('#skF_4') | v2_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_5119])).
% 15.34/7.68  tff(c_12158, plain, (k1_relat_1(k2_funct_1('#skF_4'))!=k2_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_12148])).
% 15.34/7.68  tff(c_12196, plain, (~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_54, c_12158])).
% 15.34/7.68  tff(c_12200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_372, c_132, c_124, c_12196])).
% 15.34/7.68  tff(c_12201, plain, (v2_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_12148])).
% 15.34/7.68  tff(c_12202, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_12148])).
% 15.34/7.68  tff(c_24, plain, (![A_15]: (k9_relat_1(A_15, k1_relat_1(A_15))=k2_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 15.34/7.68  tff(c_12244, plain, (k9_relat_1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'))=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12202, c_24])).
% 15.34/7.68  tff(c_12279, plain, (k9_relat_1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'))=k2_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12149, c_12244])).
% 15.34/7.68  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.34/7.68  tff(c_2173, plain, (![A_273, B_274]: (k9_relat_1(k2_funct_1(A_273), k9_relat_1(A_273, B_274))=B_274 | ~r1_tarski(B_274, k1_relat_1(A_273)) | ~v2_funct_1(A_273) | ~v1_funct_1(A_273) | ~v1_relat_1(A_273))), inference(cnfTransformation, [status(thm)], [f_111])).
% 15.34/7.68  tff(c_2191, plain, (![A_15]: (k9_relat_1(k2_funct_1(A_15), k2_relat_1(A_15))=k1_relat_1(A_15) | ~r1_tarski(k1_relat_1(A_15), k1_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2173])).
% 15.34/7.68  tff(c_2197, plain, (![A_15]: (k9_relat_1(k2_funct_1(A_15), k2_relat_1(A_15))=k1_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2191])).
% 15.34/7.68  tff(c_12318, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12279, c_2197])).
% 15.34/7.68  tff(c_12334, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_372, c_132, c_124, c_12318])).
% 15.34/7.68  tff(c_5558, plain, (![B_387, C_388, A_389]: (k6_partfun1(B_387)=k5_relat_1(k2_funct_1(C_388), C_388) | k1_xboole_0=B_387 | ~v2_funct_1(C_388) | k2_relset_1(A_389, B_387, C_388)!=B_387 | ~m1_subset_1(C_388, k1_zfmisc_1(k2_zfmisc_1(A_389, B_387))) | ~v1_funct_2(C_388, A_389, B_387) | ~v1_funct_1(C_388))), inference(cnfTransformation, [status(thm)], [f_289])).
% 15.34/7.68  tff(c_5566, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1(k2_relat_1('#skF_4')) | k2_relat_1('#skF_4')=k1_xboole_0 | ~v2_funct_1('#skF_4') | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1835, c_5558])).
% 15.34/7.68  tff(c_5586, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1(k2_relat_1('#skF_4')) | k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_132, c_1837, c_1833, c_124, c_5566])).
% 15.34/7.68  tff(c_5587, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1(k2_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_977, c_5586])).
% 15.34/7.68  tff(c_56, plain, (![A_28, B_30]: (k2_funct_1(A_28)=B_30 | k6_relat_1(k1_relat_1(A_28))!=k5_relat_1(A_28, B_30) | k2_relat_1(A_28)!=k1_relat_1(B_30) | ~v2_funct_1(A_28) | ~v1_funct_1(B_30) | ~v1_relat_1(B_30) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_155])).
% 15.34/7.68  tff(c_3362, plain, (![A_319, B_320]: (k2_funct_1(A_319)=B_320 | k6_partfun1(k1_relat_1(A_319))!=k5_relat_1(A_319, B_320) | k2_relat_1(A_319)!=k1_relat_1(B_320) | ~v2_funct_1(A_319) | ~v1_funct_1(B_320) | ~v1_relat_1(B_320) | ~v1_funct_1(A_319) | ~v1_relat_1(A_319))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_56])).
% 15.34/7.68  tff(c_32484, plain, (![A_893, B_894]: (k2_funct_1(k2_funct_1(A_893))=B_894 | k5_relat_1(k2_funct_1(A_893), B_894)!=k6_partfun1(k2_relat_1(A_893)) | k2_relat_1(k2_funct_1(A_893))!=k1_relat_1(B_894) | ~v2_funct_1(k2_funct_1(A_893)) | ~v1_funct_1(B_894) | ~v1_relat_1(B_894) | ~v1_funct_1(k2_funct_1(A_893)) | ~v1_relat_1(k2_funct_1(A_893)) | ~v2_funct_1(A_893) | ~v1_funct_1(A_893) | ~v1_relat_1(A_893))), inference(superposition, [status(thm), theory('equality')], [c_54, c_3362])).
% 15.34/7.68  tff(c_32492, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4' | k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5587, c_32484])).
% 15.34/7.68  tff(c_32503, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_372, c_132, c_124, c_12149, c_3338, c_12201, c_12334, c_32492])).
% 15.34/7.68  tff(c_3770, plain, (![C_331, B_332, A_333]: (v1_funct_2(k2_funct_1(C_331), B_332, A_333) | k2_relset_1(A_333, B_332, C_331)!=B_332 | ~v2_funct_1(C_331) | ~m1_subset_1(C_331, k1_zfmisc_1(k2_zfmisc_1(A_333, B_332))) | ~v1_funct_2(C_331, A_333, B_332) | ~v1_funct_1(C_331))), inference(cnfTransformation, [status(thm)], [f_273])).
% 15.34/7.68  tff(c_3773, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1835, c_3770])).
% 15.34/7.68  tff(c_3788, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_1837, c_124, c_1833, c_3773])).
% 15.34/7.68  tff(c_110, plain, (![A_67]: (m1_subset_1(A_67, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_67), k2_relat_1(A_67)))) | ~v1_funct_1(A_67) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_299])).
% 15.34/7.68  tff(c_1767, plain, (![A_67]: (k2_relset_1(k1_relat_1(A_67), k2_relat_1(A_67), A_67)=k2_relat_1(A_67) | ~v1_funct_1(A_67) | ~v1_relat_1(A_67))), inference(resolution, [status(thm)], [c_110, c_1751])).
% 15.34/7.68  tff(c_12372, plain, (k2_relset_1(k1_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12334, c_1767])).
% 15.34/7.68  tff(c_12415, plain, (k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12149, c_3338, c_12334, c_12202, c_12372])).
% 15.34/7.68  tff(c_4107, plain, (![A_342, B_343, C_344]: (k2_tops_2(A_342, B_343, C_344)=k2_funct_1(C_344) | ~v2_funct_1(C_344) | k2_relset_1(A_342, B_343, C_344)!=B_343 | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(A_342, B_343))) | ~v1_funct_2(C_344, A_342, B_343) | ~v1_funct_1(C_344))), inference(cnfTransformation, [status(thm)], [f_323])).
% 15.34/7.68  tff(c_26315, plain, (![A_805]: (k2_tops_2(k1_relat_1(A_805), k2_relat_1(A_805), A_805)=k2_funct_1(A_805) | ~v2_funct_1(A_805) | k2_relset_1(k1_relat_1(A_805), k2_relat_1(A_805), A_805)!=k2_relat_1(A_805) | ~v1_funct_2(A_805, k1_relat_1(A_805), k2_relat_1(A_805)) | ~v1_funct_1(A_805) | ~v1_relat_1(A_805))), inference(resolution, [status(thm)], [c_110, c_4107])).
% 15.34/7.68  tff(c_26351, plain, (k2_tops_2(k1_relat_1(k2_funct_1('#skF_4')), k2_relat_1(k2_funct_1('#skF_4')), k2_funct_1('#skF_4'))=k2_funct_1(k2_funct_1('#skF_4')) | ~v2_funct_1(k2_funct_1('#skF_4')) | k2_relset_1(k1_relat_1(k2_funct_1('#skF_4')), k2_relat_1(k2_funct_1('#skF_4')), k2_funct_1('#skF_4'))!=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12334, c_26315])).
% 15.34/7.68  tff(c_26465, plain, (k2_tops_2(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k2_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12149, c_3338, c_3788, c_12202, c_12415, c_12334, c_12334, c_12202, c_12201, c_12334, c_12202, c_26351])).
% 15.34/7.68  tff(c_4113, plain, (k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_funct_1('#skF_4') | ~v2_funct_1('#skF_4') | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1835, c_4107])).
% 15.34/7.68  tff(c_4131, plain, (k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_1837, c_1833, c_124, c_4113])).
% 15.34/7.68  tff(c_122, plain, (~r2_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_345])).
% 15.34/7.68  tff(c_265, plain, (~r2_funct_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_202, c_202, c_202, c_201, c_201, c_201, c_122])).
% 15.34/7.68  tff(c_1557, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k1_relat_1('#skF_4'), k2_tops_2(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1552, c_1552, c_1552, c_265])).
% 15.34/7.68  tff(c_1834, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), k2_tops_2(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1828, c_1828, c_1828, c_1557])).
% 15.34/7.68  tff(c_4136, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), k2_tops_2(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4131, c_1834])).
% 15.34/7.68  tff(c_26521, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26465, c_4136])).
% 15.34/7.68  tff(c_32524, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32503, c_26521])).
% 15.34/7.68  tff(c_32539, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9869, c_32524])).
% 15.34/7.68  tff(c_32541, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_405])).
% 15.34/7.68  tff(c_32861, plain, (![A_931]: (m1_subset_1(A_931, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_931), k2_relat_1(A_931)))) | ~v1_funct_1(A_931) | ~v1_relat_1(A_931))), inference(cnfTransformation, [status(thm)], [f_299])).
% 15.34/7.68  tff(c_32894, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4')))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_32541, c_32861])).
% 15.34/7.68  tff(c_32918, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_372, c_132, c_16, c_32894])).
% 15.34/7.68  tff(c_18, plain, (![B_9, A_7]: (v1_xboole_0(B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_7)) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 15.34/7.68  tff(c_32954, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_32918, c_18])).
% 15.34/7.68  tff(c_32964, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32954])).
% 15.34/7.68  tff(c_209, plain, (![B_97, A_98]: (~v1_xboole_0(B_97) | B_97=A_98 | ~v1_xboole_0(A_98))), inference(cnfTransformation, [status(thm)], [f_40])).
% 15.34/7.68  tff(c_212, plain, (![A_98]: (k1_xboole_0=A_98 | ~v1_xboole_0(A_98))), inference(resolution, [status(thm)], [c_2, c_209])).
% 15.34/7.68  tff(c_32976, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_32964, c_212])).
% 15.34/7.68  tff(c_32540, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_405])).
% 15.34/7.68  tff(c_32925, plain, (![A_932, B_933, C_934]: (k2_relset_1(A_932, B_933, C_934)=k2_relat_1(C_934) | ~m1_subset_1(C_934, k1_zfmisc_1(k2_zfmisc_1(A_932, B_933))))), inference(cnfTransformation, [status(thm)], [f_169])).
% 15.34/7.68  tff(c_32931, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_362, c_32925])).
% 15.34/7.68  tff(c_32943, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32540, c_32931])).
% 15.34/7.68  tff(c_33023, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32976, c_32943])).
% 15.34/7.68  tff(c_33024, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_33023, c_224])).
% 15.34/7.68  tff(c_136, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_345])).
% 15.34/7.68  tff(c_231, plain, (![A_102]: (~v1_xboole_0(u1_struct_0(A_102)) | ~l1_struct_0(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_311])).
% 15.34/7.68  tff(c_237, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_201, c_231])).
% 15.34/7.68  tff(c_241, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_237])).
% 15.34/7.68  tff(c_242, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_136, c_241])).
% 15.34/7.68  tff(c_33098, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_33024, c_242])).
% 15.34/7.68  tff(c_33103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32964, c_33098])).
% 15.34/7.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.34/7.68  
% 15.34/7.68  Inference rules
% 15.34/7.68  ----------------------
% 15.34/7.68  #Ref     : 16
% 15.34/7.68  #Sup     : 7378
% 15.34/7.68  #Fact    : 0
% 15.34/7.68  #Define  : 0
% 15.34/7.68  #Split   : 15
% 15.34/7.68  #Chain   : 0
% 15.34/7.68  #Close   : 0
% 15.34/7.68  
% 15.34/7.68  Ordering : KBO
% 15.34/7.68  
% 15.34/7.68  Simplification rules
% 15.34/7.68  ----------------------
% 15.34/7.68  #Subsume      : 2305
% 15.34/7.68  #Demod        : 6765
% 15.34/7.68  #Tautology    : 2667
% 15.34/7.68  #SimpNegUnit  : 1636
% 15.34/7.68  #BackRed      : 118
% 15.34/7.68  
% 15.34/7.68  #Partial instantiations: 0
% 15.34/7.68  #Strategies tried      : 1
% 15.34/7.68  
% 15.34/7.68  Timing (in seconds)
% 15.34/7.68  ----------------------
% 15.77/7.68  Preprocessing        : 0.43
% 15.77/7.68  Parsing              : 0.23
% 15.77/7.68  CNF conversion       : 0.03
% 15.77/7.68  Main loop            : 6.41
% 15.77/7.68  Inferencing          : 1.18
% 15.77/7.68  Reduction            : 3.22
% 15.77/7.68  Demodulation         : 2.68
% 15.77/7.68  BG Simplification    : 0.11
% 15.77/7.68  Subsumption          : 1.62
% 15.77/7.68  Abstraction          : 0.17
% 15.77/7.68  MUC search           : 0.00
% 15.77/7.68  Cooper               : 0.00
% 15.77/7.68  Total                : 6.90
% 15.77/7.68  Index Insertion      : 0.00
% 15.77/7.68  Index Deletion       : 0.00
% 15.77/7.68  Index Matching       : 0.00
% 15.77/7.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
