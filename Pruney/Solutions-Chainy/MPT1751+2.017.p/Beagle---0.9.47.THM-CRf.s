%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:00 EST 2020

% Result     : Theorem 12.72s
% Output     : CNFRefutation 12.72s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 477 expanded)
%              Number of leaves         :   50 ( 186 expanded)
%              Depth                    :   17
%              Number of atoms          :  293 (2131 expanded)
%              Number of equality atoms :   55 ( 408 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_194,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                       => ( r1_tarski(E,u1_struct_0(C))
                         => k7_relset_1(u1_struct_0(B),u1_struct_0(A),D,E) = k7_relset_1(u1_struct_0(C),u1_struct_0(A),k2_tmap_1(B,A,D,C),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tmap_1)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_86,axiom,(
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

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_151,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_158,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_78,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_48,plain,(
    ! [A_41] :
      ( l1_struct_0(A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_68,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_58,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_100,plain,(
    ! [B_95,A_96] :
      ( v1_relat_1(B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_96))
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_103,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_62,c_100])).

tff(c_112,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_103])).

tff(c_80,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_64,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_163,plain,(
    ! [A_111,B_112,C_113] :
      ( k1_relset_1(A_111,B_112,C_113) = k1_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_171,plain,(
    k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_163])).

tff(c_505,plain,(
    ! [B_193,A_194,C_195] :
      ( k1_xboole_0 = B_193
      | k1_relset_1(A_194,B_193,C_195) = A_194
      | ~ v1_funct_2(C_195,A_194,B_193)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_194,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_515,plain,
    ( u1_struct_0('#skF_1') = k1_xboole_0
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4') = u1_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_505])).

tff(c_524,plain,
    ( u1_struct_0('#skF_1') = k1_xboole_0
    | u1_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_171,c_515])).

tff(c_526,plain,(
    u1_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_524])).

tff(c_534,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_64])).

tff(c_464,plain,(
    ! [A_183,B_184,C_185,D_186] :
      ( k2_partfun1(A_183,B_184,C_185,D_186) = k7_relat_1(C_185,D_186)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ v1_funct_1(C_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_471,plain,(
    ! [D_186] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_186) = k7_relat_1('#skF_4',D_186)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_464])).

tff(c_479,plain,(
    ! [D_186] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_186) = k7_relat_1('#skF_4',D_186) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_471])).

tff(c_527,plain,(
    ! [D_186] : k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_186) = k7_relat_1('#skF_4',D_186) ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_479])).

tff(c_532,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_62])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_74,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_72,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_834,plain,(
    ! [A_208,B_209,C_210,D_211] :
      ( k2_partfun1(u1_struct_0(A_208),u1_struct_0(B_209),C_210,u1_struct_0(D_211)) = k2_tmap_1(A_208,B_209,C_210,D_211)
      | ~ m1_pre_topc(D_211,A_208)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_208),u1_struct_0(B_209))))
      | ~ v1_funct_2(C_210,u1_struct_0(A_208),u1_struct_0(B_209))
      | ~ v1_funct_1(C_210)
      | ~ l1_pre_topc(B_209)
      | ~ v2_pre_topc(B_209)
      | v2_struct_0(B_209)
      | ~ l1_pre_topc(A_208)
      | ~ v2_pre_topc(A_208)
      | v2_struct_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_839,plain,(
    ! [B_209,C_210,D_211] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_209),C_210,u1_struct_0(D_211)) = k2_tmap_1('#skF_2',B_209,C_210,D_211)
      | ~ m1_pre_topc(D_211,'#skF_2')
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_209))))
      | ~ v1_funct_2(C_210,u1_struct_0('#skF_2'),u1_struct_0(B_209))
      | ~ v1_funct_1(C_210)
      | ~ l1_pre_topc(B_209)
      | ~ v2_pre_topc(B_209)
      | v2_struct_0(B_209)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_834])).

tff(c_850,plain,(
    ! [B_209,C_210,D_211] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_209),C_210,u1_struct_0(D_211)) = k2_tmap_1('#skF_2',B_209,C_210,D_211)
      | ~ m1_pre_topc(D_211,'#skF_2')
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_209))))
      | ~ v1_funct_2(C_210,k1_relat_1('#skF_4'),u1_struct_0(B_209))
      | ~ v1_funct_1(C_210)
      | ~ l1_pre_topc(B_209)
      | ~ v2_pre_topc(B_209)
      | v2_struct_0(B_209)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_526,c_526,c_839])).

tff(c_860,plain,(
    ! [B_212,C_213,D_214] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_212),C_213,u1_struct_0(D_214)) = k2_tmap_1('#skF_2',B_212,C_213,D_214)
      | ~ m1_pre_topc(D_214,'#skF_2')
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_212))))
      | ~ v1_funct_2(C_213,k1_relat_1('#skF_4'),u1_struct_0(B_212))
      | ~ v1_funct_1(C_213)
      | ~ l1_pre_topc(B_212)
      | ~ v2_pre_topc(B_212)
      | v2_struct_0(B_212) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_850])).

tff(c_865,plain,(
    ! [D_214] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_214)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_214)
      | ~ m1_pre_topc(D_214,'#skF_2')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_532,c_860])).

tff(c_880,plain,(
    ! [D_214] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_214)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_214)
      | ~ m1_pre_topc(D_214,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66,c_534,c_527,c_865])).

tff(c_1049,plain,(
    ! [D_225] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_225)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_225)
      | ~ m1_pre_topc(D_225,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_880])).

tff(c_14,plain,(
    ! [A_10,C_14,B_13] :
      ( k9_relat_1(k7_relat_1(A_10,C_14),B_13) = k9_relat_1(A_10,B_13)
      | ~ r1_tarski(B_13,C_14)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1066,plain,(
    ! [D_225,B_13] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_225),B_13) = k9_relat_1('#skF_4',B_13)
      | ~ r1_tarski(B_13,u1_struct_0(D_225))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_225,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1049,c_14])).

tff(c_2368,plain,(
    ! [D_361,B_362] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_361),B_362) = k9_relat_1('#skF_4',B_362)
      | ~ r1_tarski(B_362,u1_struct_0(D_361))
      | ~ m1_pre_topc(D_361,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_1066])).

tff(c_2410,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_2368])).

tff(c_2424,plain,(
    k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2410])).

tff(c_200,plain,(
    ! [A_126,B_127,C_128,D_129] :
      ( k7_relset_1(A_126,B_127,C_128,D_129) = k9_relat_1(C_128,D_129)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_232,plain,(
    ! [D_134] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_134) = k9_relat_1('#skF_4',D_134) ),
    inference(resolution,[status(thm)],[c_62,c_200])).

tff(c_18,plain,(
    ! [A_17,B_18,C_19,D_20] :
      ( m1_subset_1(k7_relset_1(A_17,B_18,C_19,D_20),k1_zfmisc_1(B_18))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_238,plain,(
    ! [D_134] :
      ( m1_subset_1(k9_relat_1('#skF_4',D_134),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_18])).

tff(c_246,plain,(
    ! [D_135] : m1_subset_1(k9_relat_1('#skF_4',D_135),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_238])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_254,plain,(
    ! [D_135] : r1_tarski(k9_relat_1('#skF_4',D_135),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_246,c_4])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_881,plain,(
    ! [D_214] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_214)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_214)
      | ~ m1_pre_topc(D_214,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_880])).

tff(c_815,plain,(
    ! [D_207] : k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_207) = k7_relat_1('#skF_4',D_207) ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_479])).

tff(c_36,plain,(
    ! [A_31,B_32,C_33,D_34] :
      ( m1_subset_1(k2_partfun1(A_31,B_32,C_33,D_34),k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_821,plain,(
    ! [D_207] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_207),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_815,c_36])).

tff(c_891,plain,(
    ! [D_215] : m1_subset_1(k7_relat_1('#skF_4',D_215),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_532,c_821])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_915,plain,(
    ! [D_215] :
      ( v1_relat_1(k7_relat_1('#skF_4',D_215))
      | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_891,c_8])).

tff(c_937,plain,(
    ! [D_215] : v1_relat_1(k7_relat_1('#skF_4',D_215)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_915])).

tff(c_279,plain,(
    ! [A_145,B_146,C_147,D_148] :
      ( v1_funct_1(k2_partfun1(A_145,B_146,C_147,D_148))
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146)))
      | ~ v1_funct_1(C_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_284,plain,(
    ! [D_148] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_148))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_279])).

tff(c_291,plain,(
    ! [D_148] : v1_funct_1(k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_148)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_284])).

tff(c_481,plain,(
    ! [D_148] : v1_funct_1(k7_relat_1('#skF_4',D_148)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_291])).

tff(c_141,plain,(
    ! [B_101,A_102] :
      ( m1_subset_1(u1_struct_0(B_101),k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ m1_pre_topc(B_101,A_102)
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_149,plain,(
    ! [B_101,A_102] :
      ( r1_tarski(u1_struct_0(B_101),u1_struct_0(A_102))
      | ~ m1_pre_topc(B_101,A_102)
      | ~ l1_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_141,c_4])).

tff(c_544,plain,(
    ! [B_101] :
      ( r1_tarski(u1_struct_0(B_101),k1_relat_1('#skF_4'))
      | ~ m1_pre_topc(B_101,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_149])).

tff(c_710,plain,(
    ! [B_199] :
      ( r1_tarski(u1_struct_0(B_199),k1_relat_1('#skF_4'))
      | ~ m1_pre_topc(B_199,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_544])).

tff(c_16,plain,(
    ! [B_16,A_15] :
      ( k1_relat_1(k7_relat_1(B_16,A_15)) = A_15
      | ~ r1_tarski(A_15,k1_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_713,plain,(
    ! [B_199] :
      ( k1_relat_1(k7_relat_1('#skF_4',u1_struct_0(B_199))) = u1_struct_0(B_199)
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(B_199,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_710,c_16])).

tff(c_1011,plain,(
    ! [B_224] :
      ( k1_relat_1(k7_relat_1('#skF_4',u1_struct_0(B_224))) = u1_struct_0(B_224)
      | ~ m1_pre_topc(B_224,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_713])).

tff(c_333,plain,(
    ! [B_158,A_159] :
      ( m1_subset_1(B_158,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_158),A_159)))
      | ~ r1_tarski(k2_relat_1(B_158),A_159)
      | ~ v1_funct_1(B_158)
      | ~ v1_relat_1(B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_366,plain,(
    ! [B_158,A_159] :
      ( r1_tarski(B_158,k2_zfmisc_1(k1_relat_1(B_158),A_159))
      | ~ r1_tarski(k2_relat_1(B_158),A_159)
      | ~ v1_funct_1(B_158)
      | ~ v1_relat_1(B_158) ) ),
    inference(resolution,[status(thm)],[c_333,c_4])).

tff(c_1020,plain,(
    ! [B_224,A_159] :
      ( r1_tarski(k7_relat_1('#skF_4',u1_struct_0(B_224)),k2_zfmisc_1(u1_struct_0(B_224),A_159))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',u1_struct_0(B_224))),A_159)
      | ~ v1_funct_1(k7_relat_1('#skF_4',u1_struct_0(B_224)))
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0(B_224)))
      | ~ m1_pre_topc(B_224,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1011,c_366])).

tff(c_3406,plain,(
    ! [B_490,A_491] :
      ( r1_tarski(k7_relat_1('#skF_4',u1_struct_0(B_490)),k2_zfmisc_1(u1_struct_0(B_490),A_491))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',u1_struct_0(B_490))),A_491)
      | ~ m1_pre_topc(B_490,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_937,c_481,c_1020])).

tff(c_5254,plain,(
    ! [D_663,A_664] :
      ( r1_tarski(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_663),k2_zfmisc_1(u1_struct_0(D_663),A_664))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_663))),A_664)
      | ~ m1_pre_topc(D_663,'#skF_2')
      | ~ m1_pre_topc(D_663,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_881,c_3406])).

tff(c_5264,plain,(
    ! [D_663,A_664] :
      ( r1_tarski(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_663),k2_zfmisc_1(u1_struct_0(D_663),A_664))
      | ~ r1_tarski(k9_relat_1('#skF_4',u1_struct_0(D_663)),A_664)
      | ~ m1_pre_topc(D_663,'#skF_2')
      | ~ m1_pre_topc(D_663,'#skF_2')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_5254])).

tff(c_5269,plain,(
    ! [D_665,A_666] :
      ( r1_tarski(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_665),k2_zfmisc_1(u1_struct_0(D_665),A_666))
      | ~ r1_tarski(k9_relat_1('#skF_4',u1_struct_0(D_665)),A_666)
      | ~ m1_pre_topc(D_665,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_5264])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_207,plain,(
    ! [A_126,B_127,A_1,D_129] :
      ( k7_relset_1(A_126,B_127,A_1,D_129) = k9_relat_1(A_1,D_129)
      | ~ r1_tarski(A_1,k2_zfmisc_1(A_126,B_127)) ) ),
    inference(resolution,[status(thm)],[c_6,c_200])).

tff(c_13665,plain,(
    ! [D_1322,A_1323,D_1324] :
      ( k7_relset_1(u1_struct_0(D_1322),A_1323,k2_tmap_1('#skF_2','#skF_1','#skF_4',D_1322),D_1324) = k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_1322),D_1324)
      | ~ r1_tarski(k9_relat_1('#skF_4',u1_struct_0(D_1322)),A_1323)
      | ~ m1_pre_topc(D_1322,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_5269,c_207])).

tff(c_13679,plain,(
    ! [D_1325,D_1326] :
      ( k7_relset_1(u1_struct_0(D_1325),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_1325),D_1326) = k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_1325),D_1326)
      | ~ m1_pre_topc(D_1325,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_254,c_13665])).

tff(c_206,plain,(
    ! [D_129] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_129) = k9_relat_1('#skF_4',D_129) ),
    inference(resolution,[status(thm)],[c_62,c_200])).

tff(c_56,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_231,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_56])).

tff(c_13694,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13679,c_231])).

tff(c_13709,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2424,c_13694])).

tff(c_13710,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_524])).

tff(c_50,plain,(
    ! [A_42] :
      ( ~ v1_xboole_0(u1_struct_0(A_42))
      | ~ l1_struct_0(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_13739,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_13710,c_50])).

tff(c_13749,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_13739])).

tff(c_13750,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_13749])).

tff(c_13754,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_13750])).

tff(c_13758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_13754])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:09:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.72/5.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.72/5.18  
% 12.72/5.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.72/5.18  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.72/5.18  
% 12.72/5.18  %Foreground sorts:
% 12.72/5.18  
% 12.72/5.18  
% 12.72/5.18  %Background operators:
% 12.72/5.18  
% 12.72/5.18  
% 12.72/5.18  %Foreground operators:
% 12.72/5.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.72/5.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.72/5.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.72/5.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.72/5.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.72/5.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.72/5.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.72/5.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.72/5.18  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 12.72/5.18  tff('#skF_5', type, '#skF_5': $i).
% 12.72/5.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.72/5.18  tff('#skF_2', type, '#skF_2': $i).
% 12.72/5.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.72/5.18  tff('#skF_3', type, '#skF_3': $i).
% 12.72/5.18  tff('#skF_1', type, '#skF_1': $i).
% 12.72/5.18  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.72/5.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.72/5.18  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 12.72/5.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.72/5.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.72/5.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.72/5.18  tff('#skF_4', type, '#skF_4': $i).
% 12.72/5.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.72/5.18  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 12.72/5.18  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 12.72/5.18  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.72/5.18  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 12.72/5.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.72/5.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.72/5.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.72/5.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.72/5.18  
% 12.72/5.20  tff(f_194, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(E, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(B), u1_struct_0(A), D, E) = k7_relset_1(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tmap_1)).
% 12.72/5.20  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 12.72/5.20  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 12.72/5.20  tff(f_39, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 12.72/5.20  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 12.72/5.20  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.72/5.20  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 12.72/5.20  tff(f_100, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 12.72/5.20  tff(f_151, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 12.72/5.20  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 12.72/5.20  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 12.72/5.20  tff(f_60, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 12.72/5.20  tff(f_30, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.72/5.20  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 12.72/5.20  tff(f_94, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 12.72/5.20  tff(f_158, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 12.72/5.20  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 12.72/5.20  tff(f_112, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 12.72/5.20  tff(f_124, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 12.72/5.20  tff(c_78, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_194])).
% 12.72/5.20  tff(c_48, plain, (![A_41]: (l1_struct_0(A_41) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_116])).
% 12.72/5.20  tff(c_82, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_194])).
% 12.72/5.20  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 12.72/5.20  tff(c_68, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 12.72/5.20  tff(c_58, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 12.72/5.20  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.72/5.20  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_194])).
% 12.72/5.20  tff(c_100, plain, (![B_95, A_96]: (v1_relat_1(B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(A_96)) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.72/5.20  tff(c_103, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_62, c_100])).
% 12.72/5.20  tff(c_112, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_103])).
% 12.72/5.20  tff(c_80, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_194])).
% 12.72/5.20  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_194])).
% 12.72/5.20  tff(c_64, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 12.72/5.20  tff(c_163, plain, (![A_111, B_112, C_113]: (k1_relset_1(A_111, B_112, C_113)=k1_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.72/5.20  tff(c_171, plain, (k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_163])).
% 12.72/5.20  tff(c_505, plain, (![B_193, A_194, C_195]: (k1_xboole_0=B_193 | k1_relset_1(A_194, B_193, C_195)=A_194 | ~v1_funct_2(C_195, A_194, B_193) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_194, B_193))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.72/5.20  tff(c_515, plain, (u1_struct_0('#skF_1')=k1_xboole_0 | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4')=u1_struct_0('#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_505])).
% 12.72/5.20  tff(c_524, plain, (u1_struct_0('#skF_1')=k1_xboole_0 | u1_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_171, c_515])).
% 12.72/5.20  tff(c_526, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_524])).
% 12.72/5.20  tff(c_534, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_526, c_64])).
% 12.72/5.20  tff(c_464, plain, (![A_183, B_184, C_185, D_186]: (k2_partfun1(A_183, B_184, C_185, D_186)=k7_relat_1(C_185, D_186) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | ~v1_funct_1(C_185))), inference(cnfTransformation, [status(thm)], [f_100])).
% 12.72/5.20  tff(c_471, plain, (![D_186]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_186)=k7_relat_1('#skF_4', D_186) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_464])).
% 12.72/5.20  tff(c_479, plain, (![D_186]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_186)=k7_relat_1('#skF_4', D_186))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_471])).
% 12.72/5.20  tff(c_527, plain, (![D_186]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_186)=k7_relat_1('#skF_4', D_186))), inference(demodulation, [status(thm), theory('equality')], [c_526, c_479])).
% 12.72/5.20  tff(c_532, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_526, c_62])).
% 12.72/5.20  tff(c_76, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 12.72/5.20  tff(c_74, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 12.72/5.20  tff(c_72, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 12.72/5.20  tff(c_834, plain, (![A_208, B_209, C_210, D_211]: (k2_partfun1(u1_struct_0(A_208), u1_struct_0(B_209), C_210, u1_struct_0(D_211))=k2_tmap_1(A_208, B_209, C_210, D_211) | ~m1_pre_topc(D_211, A_208) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_208), u1_struct_0(B_209)))) | ~v1_funct_2(C_210, u1_struct_0(A_208), u1_struct_0(B_209)) | ~v1_funct_1(C_210) | ~l1_pre_topc(B_209) | ~v2_pre_topc(B_209) | v2_struct_0(B_209) | ~l1_pre_topc(A_208) | ~v2_pre_topc(A_208) | v2_struct_0(A_208))), inference(cnfTransformation, [status(thm)], [f_151])).
% 12.72/5.20  tff(c_839, plain, (![B_209, C_210, D_211]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_209), C_210, u1_struct_0(D_211))=k2_tmap_1('#skF_2', B_209, C_210, D_211) | ~m1_pre_topc(D_211, '#skF_2') | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_209)))) | ~v1_funct_2(C_210, u1_struct_0('#skF_2'), u1_struct_0(B_209)) | ~v1_funct_1(C_210) | ~l1_pre_topc(B_209) | ~v2_pre_topc(B_209) | v2_struct_0(B_209) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_526, c_834])).
% 12.72/5.20  tff(c_850, plain, (![B_209, C_210, D_211]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_209), C_210, u1_struct_0(D_211))=k2_tmap_1('#skF_2', B_209, C_210, D_211) | ~m1_pre_topc(D_211, '#skF_2') | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_209)))) | ~v1_funct_2(C_210, k1_relat_1('#skF_4'), u1_struct_0(B_209)) | ~v1_funct_1(C_210) | ~l1_pre_topc(B_209) | ~v2_pre_topc(B_209) | v2_struct_0(B_209) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_526, c_526, c_839])).
% 12.72/5.20  tff(c_860, plain, (![B_212, C_213, D_214]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_212), C_213, u1_struct_0(D_214))=k2_tmap_1('#skF_2', B_212, C_213, D_214) | ~m1_pre_topc(D_214, '#skF_2') | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_212)))) | ~v1_funct_2(C_213, k1_relat_1('#skF_4'), u1_struct_0(B_212)) | ~v1_funct_1(C_213) | ~l1_pre_topc(B_212) | ~v2_pre_topc(B_212) | v2_struct_0(B_212))), inference(negUnitSimplification, [status(thm)], [c_76, c_850])).
% 12.72/5.20  tff(c_865, plain, (![D_214]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_214))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_214) | ~m1_pre_topc(D_214, '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_532, c_860])).
% 12.72/5.20  tff(c_880, plain, (![D_214]: (k7_relat_1('#skF_4', u1_struct_0(D_214))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_214) | ~m1_pre_topc(D_214, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66, c_534, c_527, c_865])).
% 12.72/5.20  tff(c_1049, plain, (![D_225]: (k7_relat_1('#skF_4', u1_struct_0(D_225))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_225) | ~m1_pre_topc(D_225, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_82, c_880])).
% 12.72/5.20  tff(c_14, plain, (![A_10, C_14, B_13]: (k9_relat_1(k7_relat_1(A_10, C_14), B_13)=k9_relat_1(A_10, B_13) | ~r1_tarski(B_13, C_14) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.72/5.20  tff(c_1066, plain, (![D_225, B_13]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_225), B_13)=k9_relat_1('#skF_4', B_13) | ~r1_tarski(B_13, u1_struct_0(D_225)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_225, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1049, c_14])).
% 12.72/5.20  tff(c_2368, plain, (![D_361, B_362]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_361), B_362)=k9_relat_1('#skF_4', B_362) | ~r1_tarski(B_362, u1_struct_0(D_361)) | ~m1_pre_topc(D_361, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_1066])).
% 12.72/5.20  tff(c_2410, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_2368])).
% 12.72/5.20  tff(c_2424, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2410])).
% 12.72/5.20  tff(c_200, plain, (![A_126, B_127, C_128, D_129]: (k7_relset_1(A_126, B_127, C_128, D_129)=k9_relat_1(C_128, D_129) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.72/5.20  tff(c_232, plain, (![D_134]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_134)=k9_relat_1('#skF_4', D_134))), inference(resolution, [status(thm)], [c_62, c_200])).
% 12.72/5.20  tff(c_18, plain, (![A_17, B_18, C_19, D_20]: (m1_subset_1(k7_relset_1(A_17, B_18, C_19, D_20), k1_zfmisc_1(B_18)) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.72/5.20  tff(c_238, plain, (![D_134]: (m1_subset_1(k9_relat_1('#skF_4', D_134), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_232, c_18])).
% 12.72/5.20  tff(c_246, plain, (![D_135]: (m1_subset_1(k9_relat_1('#skF_4', D_135), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_238])).
% 12.72/5.20  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 12.72/5.20  tff(c_254, plain, (![D_135]: (r1_tarski(k9_relat_1('#skF_4', D_135), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_246, c_4])).
% 12.72/5.20  tff(c_12, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.72/5.20  tff(c_881, plain, (![D_214]: (k7_relat_1('#skF_4', u1_struct_0(D_214))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_214) | ~m1_pre_topc(D_214, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_82, c_880])).
% 12.72/5.20  tff(c_815, plain, (![D_207]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_207)=k7_relat_1('#skF_4', D_207))), inference(demodulation, [status(thm), theory('equality')], [c_526, c_479])).
% 12.72/5.20  tff(c_36, plain, (![A_31, B_32, C_33, D_34]: (m1_subset_1(k2_partfun1(A_31, B_32, C_33, D_34), k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_1(C_33))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.72/5.20  tff(c_821, plain, (![D_207]: (m1_subset_1(k7_relat_1('#skF_4', D_207), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_815, c_36])).
% 12.72/5.20  tff(c_891, plain, (![D_215]: (m1_subset_1(k7_relat_1('#skF_4', D_215), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_532, c_821])).
% 12.72/5.20  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.72/5.20  tff(c_915, plain, (![D_215]: (v1_relat_1(k7_relat_1('#skF_4', D_215)) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_891, c_8])).
% 12.72/5.20  tff(c_937, plain, (![D_215]: (v1_relat_1(k7_relat_1('#skF_4', D_215)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_915])).
% 12.72/5.20  tff(c_279, plain, (![A_145, B_146, C_147, D_148]: (v1_funct_1(k2_partfun1(A_145, B_146, C_147, D_148)) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))) | ~v1_funct_1(C_147))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.72/5.20  tff(c_284, plain, (![D_148]: (v1_funct_1(k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_148)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_279])).
% 12.72/5.20  tff(c_291, plain, (![D_148]: (v1_funct_1(k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_148)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_284])).
% 12.72/5.20  tff(c_481, plain, (![D_148]: (v1_funct_1(k7_relat_1('#skF_4', D_148)))), inference(demodulation, [status(thm), theory('equality')], [c_479, c_291])).
% 12.72/5.20  tff(c_141, plain, (![B_101, A_102]: (m1_subset_1(u1_struct_0(B_101), k1_zfmisc_1(u1_struct_0(A_102))) | ~m1_pre_topc(B_101, A_102) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_158])).
% 12.72/5.20  tff(c_149, plain, (![B_101, A_102]: (r1_tarski(u1_struct_0(B_101), u1_struct_0(A_102)) | ~m1_pre_topc(B_101, A_102) | ~l1_pre_topc(A_102))), inference(resolution, [status(thm)], [c_141, c_4])).
% 12.72/5.20  tff(c_544, plain, (![B_101]: (r1_tarski(u1_struct_0(B_101), k1_relat_1('#skF_4')) | ~m1_pre_topc(B_101, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_526, c_149])).
% 12.72/5.20  tff(c_710, plain, (![B_199]: (r1_tarski(u1_struct_0(B_199), k1_relat_1('#skF_4')) | ~m1_pre_topc(B_199, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_544])).
% 12.72/5.20  tff(c_16, plain, (![B_16, A_15]: (k1_relat_1(k7_relat_1(B_16, A_15))=A_15 | ~r1_tarski(A_15, k1_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.72/5.20  tff(c_713, plain, (![B_199]: (k1_relat_1(k7_relat_1('#skF_4', u1_struct_0(B_199)))=u1_struct_0(B_199) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(B_199, '#skF_2'))), inference(resolution, [status(thm)], [c_710, c_16])).
% 12.72/5.20  tff(c_1011, plain, (![B_224]: (k1_relat_1(k7_relat_1('#skF_4', u1_struct_0(B_224)))=u1_struct_0(B_224) | ~m1_pre_topc(B_224, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_713])).
% 12.72/5.20  tff(c_333, plain, (![B_158, A_159]: (m1_subset_1(B_158, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_158), A_159))) | ~r1_tarski(k2_relat_1(B_158), A_159) | ~v1_funct_1(B_158) | ~v1_relat_1(B_158))), inference(cnfTransformation, [status(thm)], [f_112])).
% 12.72/5.20  tff(c_366, plain, (![B_158, A_159]: (r1_tarski(B_158, k2_zfmisc_1(k1_relat_1(B_158), A_159)) | ~r1_tarski(k2_relat_1(B_158), A_159) | ~v1_funct_1(B_158) | ~v1_relat_1(B_158))), inference(resolution, [status(thm)], [c_333, c_4])).
% 12.72/5.20  tff(c_1020, plain, (![B_224, A_159]: (r1_tarski(k7_relat_1('#skF_4', u1_struct_0(B_224)), k2_zfmisc_1(u1_struct_0(B_224), A_159)) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', u1_struct_0(B_224))), A_159) | ~v1_funct_1(k7_relat_1('#skF_4', u1_struct_0(B_224))) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0(B_224))) | ~m1_pre_topc(B_224, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1011, c_366])).
% 12.72/5.20  tff(c_3406, plain, (![B_490, A_491]: (r1_tarski(k7_relat_1('#skF_4', u1_struct_0(B_490)), k2_zfmisc_1(u1_struct_0(B_490), A_491)) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', u1_struct_0(B_490))), A_491) | ~m1_pre_topc(B_490, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_937, c_481, c_1020])).
% 12.72/5.20  tff(c_5254, plain, (![D_663, A_664]: (r1_tarski(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_663), k2_zfmisc_1(u1_struct_0(D_663), A_664)) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_663))), A_664) | ~m1_pre_topc(D_663, '#skF_2') | ~m1_pre_topc(D_663, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_881, c_3406])).
% 12.72/5.20  tff(c_5264, plain, (![D_663, A_664]: (r1_tarski(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_663), k2_zfmisc_1(u1_struct_0(D_663), A_664)) | ~r1_tarski(k9_relat_1('#skF_4', u1_struct_0(D_663)), A_664) | ~m1_pre_topc(D_663, '#skF_2') | ~m1_pre_topc(D_663, '#skF_2') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_5254])).
% 12.72/5.20  tff(c_5269, plain, (![D_665, A_666]: (r1_tarski(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_665), k2_zfmisc_1(u1_struct_0(D_665), A_666)) | ~r1_tarski(k9_relat_1('#skF_4', u1_struct_0(D_665)), A_666) | ~m1_pre_topc(D_665, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_5264])).
% 12.72/5.20  tff(c_6, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 12.72/5.20  tff(c_207, plain, (![A_126, B_127, A_1, D_129]: (k7_relset_1(A_126, B_127, A_1, D_129)=k9_relat_1(A_1, D_129) | ~r1_tarski(A_1, k2_zfmisc_1(A_126, B_127)))), inference(resolution, [status(thm)], [c_6, c_200])).
% 12.72/5.20  tff(c_13665, plain, (![D_1322, A_1323, D_1324]: (k7_relset_1(u1_struct_0(D_1322), A_1323, k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_1322), D_1324)=k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_1322), D_1324) | ~r1_tarski(k9_relat_1('#skF_4', u1_struct_0(D_1322)), A_1323) | ~m1_pre_topc(D_1322, '#skF_2'))), inference(resolution, [status(thm)], [c_5269, c_207])).
% 12.72/5.20  tff(c_13679, plain, (![D_1325, D_1326]: (k7_relset_1(u1_struct_0(D_1325), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_1325), D_1326)=k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_1325), D_1326) | ~m1_pre_topc(D_1325, '#skF_2'))), inference(resolution, [status(thm)], [c_254, c_13665])).
% 12.72/5.20  tff(c_206, plain, (![D_129]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_129)=k9_relat_1('#skF_4', D_129))), inference(resolution, [status(thm)], [c_62, c_200])).
% 12.72/5.20  tff(c_56, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_194])).
% 12.72/5.20  tff(c_231, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_56])).
% 12.72/5.20  tff(c_13694, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13679, c_231])).
% 12.72/5.20  tff(c_13709, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_2424, c_13694])).
% 12.72/5.20  tff(c_13710, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_524])).
% 12.72/5.20  tff(c_50, plain, (![A_42]: (~v1_xboole_0(u1_struct_0(A_42)) | ~l1_struct_0(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_124])).
% 12.72/5.20  tff(c_13739, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_13710, c_50])).
% 12.72/5.20  tff(c_13749, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_13739])).
% 12.72/5.20  tff(c_13750, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_82, c_13749])).
% 12.72/5.20  tff(c_13754, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_13750])).
% 12.72/5.20  tff(c_13758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_13754])).
% 12.72/5.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.72/5.20  
% 12.72/5.20  Inference rules
% 12.72/5.20  ----------------------
% 12.72/5.20  #Ref     : 0
% 12.72/5.20  #Sup     : 3152
% 12.72/5.20  #Fact    : 0
% 12.72/5.20  #Define  : 0
% 12.72/5.20  #Split   : 14
% 12.72/5.20  #Chain   : 0
% 12.72/5.20  #Close   : 0
% 12.72/5.20  
% 12.72/5.20  Ordering : KBO
% 12.72/5.20  
% 12.72/5.20  Simplification rules
% 12.72/5.20  ----------------------
% 12.72/5.20  #Subsume      : 564
% 12.72/5.20  #Demod        : 2491
% 12.72/5.20  #Tautology    : 543
% 12.72/5.20  #SimpNegUnit  : 180
% 12.72/5.20  #BackRed      : 75
% 12.72/5.20  
% 12.72/5.20  #Partial instantiations: 0
% 12.72/5.20  #Strategies tried      : 1
% 12.72/5.20  
% 12.72/5.20  Timing (in seconds)
% 12.72/5.20  ----------------------
% 12.72/5.20  Preprocessing        : 0.58
% 12.72/5.20  Parsing              : 0.29
% 12.72/5.20  CNF conversion       : 0.05
% 12.72/5.20  Main loop            : 3.72
% 12.72/5.20  Inferencing          : 1.12
% 12.72/5.21  Reduction            : 1.45
% 12.72/5.21  Demodulation         : 1.12
% 12.72/5.21  BG Simplification    : 0.13
% 12.72/5.21  Subsumption          : 0.80
% 12.72/5.21  Abstraction          : 0.20
% 12.72/5.21  MUC search           : 0.00
% 12.72/5.21  Cooper               : 0.00
% 12.72/5.21  Total                : 4.35
% 12.72/5.21  Index Insertion      : 0.00
% 12.72/5.21  Index Deletion       : 0.00
% 12.72/5.21  Index Matching       : 0.00
% 12.72/5.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
