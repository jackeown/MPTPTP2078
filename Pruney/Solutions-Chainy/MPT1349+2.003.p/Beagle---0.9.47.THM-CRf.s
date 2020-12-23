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
% DateTime   : Thu Dec  3 10:23:51 EST 2020

% Result     : Theorem 11.27s
% Output     : CNFRefutation 11.43s
% Verified   : 
% Statistics : Number of formulae       :  200 (2098 expanded)
%              Number of leaves         :   42 ( 786 expanded)
%              Depth                    :   16
%              Number of atoms          :  751 (13462 expanded)
%              Number of equality atoms :  103 (2479 expanded)
%              Maximal formula depth    :   34 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_tops_2 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v2_funct_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v3_tops_2,type,(
    v3_tops_2: ( $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_249,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( v3_tops_2(C,A,B)
                <=> ( k1_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(A)
                    & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_pre_topc(A,D)) = k2_pre_topc(B,k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_2)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v5_pre_topc(C,A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => r1_tarski(k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_pre_topc(A,D)),k2_pre_topc(B,k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_tops_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_144,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v2_funct_1(C) )
               => v2_funct_1(k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).

tff(f_126,axiom,(
    ! [A] :
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
               => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                  & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v3_tops_2(C,A,B)
              <=> ( k1_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(A)
                  & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v2_funct_1(C)
                  & v5_pre_topc(C,A,B)
                  & v5_pre_topc(k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_2)).

tff(f_216,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v3_tops_2(C,A,B)
              <=> ( k1_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(A)
                  & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v2_funct_1(C)
                  & ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                     => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_pre_topc(B,D)) = k2_pre_topc(A,k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tops_2)).

tff(f_165,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                      & v2_funct_1(C) )
                   => k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D) = k8_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tops_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_184,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v3_tops_2(C,A,B)
               => v3_tops_2(k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_tops_2)).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_98,plain,
    ( v3_tops_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_119,plain,(
    k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_92,plain,
    ( v3_tops_2('#skF_5','#skF_3','#skF_4')
    | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_114,plain,(
    k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_86,plain,
    ( v3_tops_2('#skF_5','#skF_3','#skF_4')
    | v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_106,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_78,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
    | k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_3')
    | ~ v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_133,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_114,c_106,c_78])).

tff(c_134,plain,(
    ~ v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_70,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_64,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_60,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_72,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_66,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_274,plain,(
    ! [A_158,B_159,C_160] :
      ( m1_subset_1('#skF_1'(A_158,B_159,C_160),k1_zfmisc_1(u1_struct_0(A_158)))
      | v5_pre_topc(C_160,A_158,B_159)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_158),u1_struct_0(B_159))))
      | ~ v1_funct_2(C_160,u1_struct_0(A_158),u1_struct_0(B_159))
      | ~ v1_funct_1(C_160)
      | ~ l1_pre_topc(B_159)
      | ~ v2_pre_topc(B_159)
      | v2_struct_0(B_159)
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_279,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_274])).

tff(c_283,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_62,c_60,c_279])).

tff(c_284,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_283])).

tff(c_285,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_284])).

tff(c_24,plain,(
    ! [A_13,B_14,C_15] :
      ( m1_subset_1(k2_tops_2(A_13,B_14,C_15),k1_zfmisc_1(k2_zfmisc_1(B_14,A_13)))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_2(C_15,A_13,B_14)
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_240,plain,(
    ! [A_155,B_156,C_157] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_155),u1_struct_0(B_156),C_157))
      | ~ v2_funct_1(C_157)
      | k2_relset_1(u1_struct_0(A_155),u1_struct_0(B_156),C_157) != k2_struct_0(B_156)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_155),u1_struct_0(B_156))))
      | ~ v1_funct_2(C_157,u1_struct_0(A_155),u1_struct_0(B_156))
      | ~ v1_funct_1(C_157)
      | ~ l1_struct_0(B_156)
      | ~ l1_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_247,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_240])).

tff(c_251,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_114,c_106,c_247])).

tff(c_252,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_251])).

tff(c_255,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_252])).

tff(c_259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_255])).

tff(c_261,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_260,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_264,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_267,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_264])).

tff(c_271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_267])).

tff(c_273,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_38,plain,(
    ! [B_42,A_38,C_44] :
      ( k1_relset_1(u1_struct_0(B_42),u1_struct_0(A_38),k2_tops_2(u1_struct_0(A_38),u1_struct_0(B_42),C_44)) = k2_struct_0(B_42)
      | ~ v2_funct_1(C_44)
      | k2_relset_1(u1_struct_0(A_38),u1_struct_0(B_42),C_44) != k2_struct_0(B_42)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_38),u1_struct_0(B_42))))
      | ~ v1_funct_2(C_44,u1_struct_0(A_38),u1_struct_0(B_42))
      | ~ v1_funct_1(C_44)
      | ~ l1_struct_0(B_42)
      | v2_struct_0(B_42)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_36,plain,(
    ! [B_42,A_38,C_44] :
      ( k2_relset_1(u1_struct_0(B_42),u1_struct_0(A_38),k2_tops_2(u1_struct_0(A_38),u1_struct_0(B_42),C_44)) = k2_struct_0(A_38)
      | ~ v2_funct_1(C_44)
      | k2_relset_1(u1_struct_0(A_38),u1_struct_0(B_42),C_44) != k2_struct_0(B_42)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_38),u1_struct_0(B_42))))
      | ~ v1_funct_2(C_44,u1_struct_0(A_38),u1_struct_0(B_42))
      | ~ v1_funct_1(C_44)
      | ~ l1_struct_0(B_42)
      | v2_struct_0(B_42)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_125,plain,(
    ! [A_121,B_122,C_123] :
      ( v1_funct_1(k2_tops_2(A_121,B_122,C_123))
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ v1_funct_2(C_123,A_121,B_122)
      | ~ v1_funct_1(C_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_128,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_125])).

tff(c_131,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_128])).

tff(c_135,plain,(
    ! [A_124,B_125,C_126] :
      ( v1_funct_2(k2_tops_2(A_124,B_125,C_126),B_125,A_124)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ v1_funct_2(C_126,A_124,B_125)
      | ~ v1_funct_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_137,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_135])).

tff(c_140,plain,(
    v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_137])).

tff(c_171,plain,(
    ! [C_134,A_135,B_136] :
      ( v5_pre_topc(C_134,A_135,B_136)
      | ~ v3_tops_2(C_134,A_135,B_136)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_135),u1_struct_0(B_136))))
      | ~ v1_funct_2(C_134,u1_struct_0(A_135),u1_struct_0(B_136))
      | ~ v1_funct_1(C_134)
      | ~ l1_pre_topc(B_136)
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_425,plain,(
    ! [B_201,A_202,C_203] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(B_201),u1_struct_0(A_202),C_203),A_202,B_201)
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(B_201),u1_struct_0(A_202),C_203),A_202,B_201)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_201),u1_struct_0(A_202),C_203),u1_struct_0(A_202),u1_struct_0(B_201))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_201),u1_struct_0(A_202),C_203))
      | ~ l1_pre_topc(B_201)
      | ~ l1_pre_topc(A_202)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_201),u1_struct_0(A_202))))
      | ~ v1_funct_2(C_203,u1_struct_0(B_201),u1_struct_0(A_202))
      | ~ v1_funct_1(C_203) ) ),
    inference(resolution,[status(thm)],[c_24,c_171])).

tff(c_432,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
    | ~ v3_tops_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_140,c_425])).

tff(c_436,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
    | ~ v3_tops_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_64,c_70,c_131,c_432])).

tff(c_437,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_436])).

tff(c_272,plain,(
    v2_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_406,plain,(
    ! [A_195,B_196,C_197] :
      ( m1_subset_1('#skF_2'(A_195,B_196,C_197),k1_zfmisc_1(u1_struct_0(B_196)))
      | v3_tops_2(C_197,A_195,B_196)
      | ~ v2_funct_1(C_197)
      | k2_relset_1(u1_struct_0(A_195),u1_struct_0(B_196),C_197) != k2_struct_0(B_196)
      | k1_relset_1(u1_struct_0(A_195),u1_struct_0(B_196),C_197) != k2_struct_0(A_195)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_195),u1_struct_0(B_196))))
      | ~ v1_funct_2(C_197,u1_struct_0(A_195),u1_struct_0(B_196))
      | ~ v1_funct_1(C_197)
      | ~ l1_pre_topc(B_196)
      | ~ v2_pre_topc(B_196)
      | ~ l1_pre_topc(A_195)
      | ~ v2_pre_topc(A_195)
      | v2_struct_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_412,plain,(
    ! [A_195,B_196,C_15] :
      ( m1_subset_1('#skF_2'(A_195,B_196,k2_tops_2(u1_struct_0(B_196),u1_struct_0(A_195),C_15)),k1_zfmisc_1(u1_struct_0(B_196)))
      | v3_tops_2(k2_tops_2(u1_struct_0(B_196),u1_struct_0(A_195),C_15),A_195,B_196)
      | ~ v2_funct_1(k2_tops_2(u1_struct_0(B_196),u1_struct_0(A_195),C_15))
      | k2_relset_1(u1_struct_0(A_195),u1_struct_0(B_196),k2_tops_2(u1_struct_0(B_196),u1_struct_0(A_195),C_15)) != k2_struct_0(B_196)
      | k1_relset_1(u1_struct_0(A_195),u1_struct_0(B_196),k2_tops_2(u1_struct_0(B_196),u1_struct_0(A_195),C_15)) != k2_struct_0(A_195)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_196),u1_struct_0(A_195),C_15),u1_struct_0(A_195),u1_struct_0(B_196))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_196),u1_struct_0(A_195),C_15))
      | ~ l1_pre_topc(B_196)
      | ~ v2_pre_topc(B_196)
      | ~ l1_pre_topc(A_195)
      | ~ v2_pre_topc(A_195)
      | v2_struct_0(A_195)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_196),u1_struct_0(A_195))))
      | ~ v1_funct_2(C_15,u1_struct_0(B_196),u1_struct_0(A_195))
      | ~ v1_funct_1(C_15) ) ),
    inference(resolution,[status(thm)],[c_24,c_406])).

tff(c_80,plain,(
    ! [D_114] :
      ( v3_tops_2('#skF_5','#skF_3','#skF_4')
      | k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_3',D_114)) = k2_pre_topc('#skF_4',k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_114))
      | ~ m1_subset_1(D_114,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_161,plain,(
    ! [D_114] :
      ( k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_3',D_114)) = k2_pre_topc('#skF_4',k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_114))
      | ~ m1_subset_1(D_114,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_80])).

tff(c_42,plain,(
    ! [B_60,A_52,C_64,D_66] :
      ( k8_relset_1(u1_struct_0(B_60),u1_struct_0(A_52),k2_tops_2(u1_struct_0(A_52),u1_struct_0(B_60),C_64),D_66) = k7_relset_1(u1_struct_0(A_52),u1_struct_0(B_60),C_64,D_66)
      | ~ v2_funct_1(C_64)
      | k2_relset_1(u1_struct_0(A_52),u1_struct_0(B_60),C_64) != k2_struct_0(B_60)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_52),u1_struct_0(B_60))))
      | ~ v1_funct_2(C_64,u1_struct_0(A_52),u1_struct_0(B_60))
      | ~ v1_funct_1(C_64)
      | ~ l1_struct_0(B_60)
      | ~ l1_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_418,plain,(
    ! [A_198,B_199,C_200] :
      ( k8_relset_1(u1_struct_0(A_198),u1_struct_0(B_199),C_200,k2_pre_topc(B_199,'#skF_2'(A_198,B_199,C_200))) != k2_pre_topc(A_198,k8_relset_1(u1_struct_0(A_198),u1_struct_0(B_199),C_200,'#skF_2'(A_198,B_199,C_200)))
      | v3_tops_2(C_200,A_198,B_199)
      | ~ v2_funct_1(C_200)
      | k2_relset_1(u1_struct_0(A_198),u1_struct_0(B_199),C_200) != k2_struct_0(B_199)
      | k1_relset_1(u1_struct_0(A_198),u1_struct_0(B_199),C_200) != k2_struct_0(A_198)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_198),u1_struct_0(B_199))))
      | ~ v1_funct_2(C_200,u1_struct_0(A_198),u1_struct_0(B_199))
      | ~ v1_funct_1(C_200)
      | ~ l1_pre_topc(B_199)
      | ~ v2_pre_topc(B_199)
      | ~ l1_pre_topc(A_198)
      | ~ v2_pre_topc(A_198)
      | v2_struct_0(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_1403,plain,(
    ! [B_258,A_259,C_260] :
      ( k8_relset_1(u1_struct_0(B_258),u1_struct_0(A_259),k2_tops_2(u1_struct_0(A_259),u1_struct_0(B_258),C_260),k2_pre_topc(A_259,'#skF_2'(B_258,A_259,k2_tops_2(u1_struct_0(A_259),u1_struct_0(B_258),C_260)))) != k2_pre_topc(B_258,k7_relset_1(u1_struct_0(A_259),u1_struct_0(B_258),C_260,'#skF_2'(B_258,A_259,k2_tops_2(u1_struct_0(A_259),u1_struct_0(B_258),C_260))))
      | v3_tops_2(k2_tops_2(u1_struct_0(A_259),u1_struct_0(B_258),C_260),B_258,A_259)
      | ~ v2_funct_1(k2_tops_2(u1_struct_0(A_259),u1_struct_0(B_258),C_260))
      | k2_relset_1(u1_struct_0(B_258),u1_struct_0(A_259),k2_tops_2(u1_struct_0(A_259),u1_struct_0(B_258),C_260)) != k2_struct_0(A_259)
      | k1_relset_1(u1_struct_0(B_258),u1_struct_0(A_259),k2_tops_2(u1_struct_0(A_259),u1_struct_0(B_258),C_260)) != k2_struct_0(B_258)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_259),u1_struct_0(B_258),C_260),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_258),u1_struct_0(A_259))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_259),u1_struct_0(B_258),C_260),u1_struct_0(B_258),u1_struct_0(A_259))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_259),u1_struct_0(B_258),C_260))
      | ~ l1_pre_topc(A_259)
      | ~ v2_pre_topc(A_259)
      | ~ l1_pre_topc(B_258)
      | ~ v2_pre_topc(B_258)
      | v2_struct_0(B_258)
      | ~ v2_funct_1(C_260)
      | k2_relset_1(u1_struct_0(A_259),u1_struct_0(B_258),C_260) != k2_struct_0(B_258)
      | ~ m1_subset_1('#skF_2'(B_258,A_259,k2_tops_2(u1_struct_0(A_259),u1_struct_0(B_258),C_260)),k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_259),u1_struct_0(B_258))))
      | ~ v1_funct_2(C_260,u1_struct_0(A_259),u1_struct_0(B_258))
      | ~ v1_funct_1(C_260)
      | ~ l1_struct_0(B_258)
      | ~ l1_struct_0(A_259) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_418])).

tff(c_5525,plain,(
    ! [A_366,B_367,C_368] :
      ( k7_relset_1(u1_struct_0(A_366),u1_struct_0(B_367),C_368,k2_pre_topc(A_366,'#skF_2'(B_367,A_366,k2_tops_2(u1_struct_0(A_366),u1_struct_0(B_367),C_368)))) != k2_pre_topc(B_367,k7_relset_1(u1_struct_0(A_366),u1_struct_0(B_367),C_368,'#skF_2'(B_367,A_366,k2_tops_2(u1_struct_0(A_366),u1_struct_0(B_367),C_368))))
      | v3_tops_2(k2_tops_2(u1_struct_0(A_366),u1_struct_0(B_367),C_368),B_367,A_366)
      | ~ v2_funct_1(k2_tops_2(u1_struct_0(A_366),u1_struct_0(B_367),C_368))
      | k2_relset_1(u1_struct_0(B_367),u1_struct_0(A_366),k2_tops_2(u1_struct_0(A_366),u1_struct_0(B_367),C_368)) != k2_struct_0(A_366)
      | k1_relset_1(u1_struct_0(B_367),u1_struct_0(A_366),k2_tops_2(u1_struct_0(A_366),u1_struct_0(B_367),C_368)) != k2_struct_0(B_367)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_366),u1_struct_0(B_367),C_368),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_367),u1_struct_0(A_366))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_366),u1_struct_0(B_367),C_368),u1_struct_0(B_367),u1_struct_0(A_366))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_366),u1_struct_0(B_367),C_368))
      | ~ l1_pre_topc(A_366)
      | ~ v2_pre_topc(A_366)
      | ~ l1_pre_topc(B_367)
      | ~ v2_pre_topc(B_367)
      | v2_struct_0(B_367)
      | ~ v2_funct_1(C_368)
      | k2_relset_1(u1_struct_0(A_366),u1_struct_0(B_367),C_368) != k2_struct_0(B_367)
      | ~ m1_subset_1('#skF_2'(B_367,A_366,k2_tops_2(u1_struct_0(A_366),u1_struct_0(B_367),C_368)),k1_zfmisc_1(u1_struct_0(A_366)))
      | ~ m1_subset_1(C_368,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_366),u1_struct_0(B_367))))
      | ~ v1_funct_2(C_368,u1_struct_0(A_366),u1_struct_0(B_367))
      | ~ v1_funct_1(C_368)
      | ~ l1_struct_0(B_367)
      | ~ l1_struct_0(A_366)
      | ~ v2_funct_1(C_368)
      | k2_relset_1(u1_struct_0(A_366),u1_struct_0(B_367),C_368) != k2_struct_0(B_367)
      | ~ m1_subset_1(k2_pre_topc(A_366,'#skF_2'(B_367,A_366,k2_tops_2(u1_struct_0(A_366),u1_struct_0(B_367),C_368))),k1_zfmisc_1(u1_struct_0(A_366)))
      | ~ m1_subset_1(C_368,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_366),u1_struct_0(B_367))))
      | ~ v1_funct_2(C_368,u1_struct_0(A_366),u1_struct_0(B_367))
      | ~ v1_funct_1(C_368)
      | ~ l1_struct_0(B_367)
      | ~ l1_struct_0(A_366) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1403])).

tff(c_5528,plain,
    ( v3_tops_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
    | ~ v2_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
    | k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_3')
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4')
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
    | ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_5525])).

tff(c_5531,plain,
    ( v3_tops_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
    | k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_3')
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4')
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | v2_struct_0('#skF_4')
    | ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_273,c_62,c_60,c_58,c_114,c_106,c_66,c_64,c_72,c_70,c_131,c_140,c_272,c_5528])).

tff(c_5532,plain,
    ( k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_3')
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4')
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_437,c_5531])).

tff(c_5533,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_5532])).

tff(c_5536,plain,
    ( v3_tops_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
    | ~ v2_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
    | k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_3')
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4')
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_412,c_5533])).

tff(c_5539,plain,
    ( v3_tops_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
    | k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_3')
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_66,c_64,c_72,c_70,c_131,c_140,c_272,c_5536])).

tff(c_5540,plain,
    ( k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_3')
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_437,c_5539])).

tff(c_5541,plain,(
    k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5540])).

tff(c_5544,plain,
    ( ~ v2_funct_1('#skF_5')
    | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_5541])).

tff(c_5547,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_273,c_62,c_60,c_58,c_114,c_106,c_5544])).

tff(c_5549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_5547])).

tff(c_5550,plain,(
    k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5540])).

tff(c_5572,plain,
    ( ~ v2_funct_1('#skF_5')
    | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_5550])).

tff(c_5575,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_273,c_62,c_60,c_58,c_114,c_106,c_5572])).

tff(c_5577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_5575])).

tff(c_5579,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_5532])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k2_pre_topc(A_3,B_4),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5578,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4')
    | k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5532])).

tff(c_5580,plain,(
    k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5578])).

tff(c_5583,plain,
    ( ~ v2_funct_1('#skF_5')
    | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_5580])).

tff(c_5586,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_273,c_62,c_60,c_58,c_114,c_106,c_5583])).

tff(c_5588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_5586])).

tff(c_5589,plain,
    ( k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4')
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_5578])).

tff(c_5609,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_5589])).

tff(c_5612,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_5609])).

tff(c_5616,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5579,c_5612])).

tff(c_5617,plain,
    ( ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_5589])).

tff(c_5689,plain,(
    k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5617])).

tff(c_5692,plain,
    ( ~ v2_funct_1('#skF_5')
    | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_5689])).

tff(c_5695,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_273,c_62,c_60,c_58,c_114,c_106,c_5692])).

tff(c_5697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_5695])).

tff(c_5698,plain,(
    ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_5617])).

tff(c_5720,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_5698])).

tff(c_5724,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_5720])).

tff(c_5725,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_436])).

tff(c_12,plain,(
    ! [C_12,A_6,B_10] :
      ( v3_tops_2(C_12,A_6,B_10)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_6),u1_struct_0(B_10),C_12),B_10,A_6)
      | ~ v5_pre_topc(C_12,A_6,B_10)
      | ~ v2_funct_1(C_12)
      | k2_relset_1(u1_struct_0(A_6),u1_struct_0(B_10),C_12) != k2_struct_0(B_10)
      | k1_relset_1(u1_struct_0(A_6),u1_struct_0(B_10),C_12) != k2_struct_0(A_6)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6),u1_struct_0(B_10))))
      | ~ v1_funct_2(C_12,u1_struct_0(A_6),u1_struct_0(B_10))
      | ~ v1_funct_1(C_12)
      | ~ l1_pre_topc(B_10)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5740,plain,
    ( v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
    | k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_5725,c_12])).

tff(c_5743,plain,(
    v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64,c_62,c_60,c_58,c_119,c_114,c_106,c_285,c_5740])).

tff(c_5745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_5743])).

tff(c_5747,plain,(
    ~ v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_5746,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5817,plain,(
    ! [A_402,B_403,C_404] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(A_402),u1_struct_0(B_403),C_404,k2_pre_topc(A_402,'#skF_1'(A_402,B_403,C_404))),k2_pre_topc(B_403,k7_relset_1(u1_struct_0(A_402),u1_struct_0(B_403),C_404,'#skF_1'(A_402,B_403,C_404))))
      | v5_pre_topc(C_404,A_402,B_403)
      | ~ m1_subset_1(C_404,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_402),u1_struct_0(B_403))))
      | ~ v1_funct_2(C_404,u1_struct_0(A_402),u1_struct_0(B_403))
      | ~ v1_funct_1(C_404)
      | ~ l1_pre_topc(B_403)
      | ~ v2_pre_topc(B_403)
      | v2_struct_0(B_403)
      | ~ l1_pre_topc(A_402)
      | ~ v2_pre_topc(A_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5825,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_4',k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))),k2_pre_topc('#skF_4',k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))))
    | v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_5817])).

tff(c_5828,plain,
    ( v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5746,c_72,c_70,c_66,c_64,c_62,c_60,c_58,c_6,c_5825])).

tff(c_5830,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_5747,c_5828])).

tff(c_5832,plain,(
    v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_5831,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_5932,plain,(
    ! [A_435,B_436,C_437] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_435),u1_struct_0(B_436),C_437))
      | ~ v2_funct_1(C_437)
      | k2_relset_1(u1_struct_0(A_435),u1_struct_0(B_436),C_437) != k2_struct_0(B_436)
      | ~ m1_subset_1(C_437,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_435),u1_struct_0(B_436))))
      | ~ v1_funct_2(C_437,u1_struct_0(A_435),u1_struct_0(B_436))
      | ~ v1_funct_1(C_437)
      | ~ l1_struct_0(B_436)
      | ~ l1_struct_0(A_435) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_5939,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_5932])).

tff(c_5943,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_114,c_106,c_5939])).

tff(c_5944,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5943])).

tff(c_5947,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_5944])).

tff(c_5951,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5947])).

tff(c_5953,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5943])).

tff(c_5952,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitRight,[status(thm)],[c_5943])).

tff(c_5965,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5952])).

tff(c_5968,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_5965])).

tff(c_5972,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5968])).

tff(c_5974,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_5952])).

tff(c_5833,plain,(
    v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_5919,plain,(
    ! [A_432,B_433,C_434] :
      ( v3_tops_2(k2_tops_2(u1_struct_0(A_432),u1_struct_0(B_433),C_434),B_433,A_432)
      | ~ v3_tops_2(C_434,A_432,B_433)
      | ~ m1_subset_1(C_434,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_432),u1_struct_0(B_433))))
      | ~ v1_funct_2(C_434,u1_struct_0(A_432),u1_struct_0(B_433))
      | ~ v1_funct_1(C_434)
      | ~ l1_pre_topc(B_433)
      | v2_struct_0(B_433)
      | ~ l1_pre_topc(A_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_5924,plain,
    ( v3_tops_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
    | ~ v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_5919])).

tff(c_5928,plain,
    ( v3_tops_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64,c_62,c_60,c_5833,c_5924])).

tff(c_5929,plain,(
    v3_tops_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_5928])).

tff(c_5835,plain,(
    ! [A_405,B_406,C_407] :
      ( v1_funct_2(k2_tops_2(A_405,B_406,C_407),B_406,A_405)
      | ~ m1_subset_1(C_407,k1_zfmisc_1(k2_zfmisc_1(A_405,B_406)))
      | ~ v1_funct_2(C_407,A_405,B_406)
      | ~ v1_funct_1(C_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5837,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_5835])).

tff(c_5840,plain,(
    v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_5837])).

tff(c_5995,plain,(
    ! [A_447,B_448,C_449,D_450] :
      ( k8_relset_1(u1_struct_0(A_447),u1_struct_0(B_448),C_449,k2_pre_topc(B_448,D_450)) = k2_pre_topc(A_447,k8_relset_1(u1_struct_0(A_447),u1_struct_0(B_448),C_449,D_450))
      | ~ m1_subset_1(D_450,k1_zfmisc_1(u1_struct_0(B_448)))
      | ~ v3_tops_2(C_449,A_447,B_448)
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_447),u1_struct_0(B_448))))
      | ~ v1_funct_2(C_449,u1_struct_0(A_447),u1_struct_0(B_448))
      | ~ v1_funct_1(C_449)
      | ~ l1_pre_topc(B_448)
      | ~ v2_pre_topc(B_448)
      | ~ l1_pre_topc(A_447)
      | ~ v2_pre_topc(A_447)
      | v2_struct_0(A_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_6141,plain,(
    ! [A_502,B_503,C_504,D_505] :
      ( k8_relset_1(u1_struct_0(A_502),u1_struct_0(B_503),k2_tops_2(u1_struct_0(B_503),u1_struct_0(A_502),C_504),k2_pre_topc(B_503,D_505)) = k2_pre_topc(A_502,k8_relset_1(u1_struct_0(A_502),u1_struct_0(B_503),k2_tops_2(u1_struct_0(B_503),u1_struct_0(A_502),C_504),D_505))
      | ~ m1_subset_1(D_505,k1_zfmisc_1(u1_struct_0(B_503)))
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(B_503),u1_struct_0(A_502),C_504),A_502,B_503)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_503),u1_struct_0(A_502),C_504),u1_struct_0(A_502),u1_struct_0(B_503))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_503),u1_struct_0(A_502),C_504))
      | ~ l1_pre_topc(B_503)
      | ~ v2_pre_topc(B_503)
      | ~ l1_pre_topc(A_502)
      | ~ v2_pre_topc(A_502)
      | v2_struct_0(A_502)
      | ~ m1_subset_1(C_504,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_503),u1_struct_0(A_502))))
      | ~ v1_funct_2(C_504,u1_struct_0(B_503),u1_struct_0(A_502))
      | ~ v1_funct_1(C_504) ) ),
    inference(resolution,[status(thm)],[c_24,c_5995])).

tff(c_6265,plain,(
    ! [B_534,A_535,C_536,D_537] :
      ( k8_relset_1(u1_struct_0(B_534),u1_struct_0(A_535),k2_tops_2(u1_struct_0(A_535),u1_struct_0(B_534),C_536),k2_pre_topc(A_535,D_537)) = k2_pre_topc(B_534,k7_relset_1(u1_struct_0(A_535),u1_struct_0(B_534),C_536,D_537))
      | ~ m1_subset_1(D_537,k1_zfmisc_1(u1_struct_0(A_535)))
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(A_535),u1_struct_0(B_534),C_536),B_534,A_535)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_535),u1_struct_0(B_534),C_536),u1_struct_0(B_534),u1_struct_0(A_535))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_535),u1_struct_0(B_534),C_536))
      | ~ l1_pre_topc(A_535)
      | ~ v2_pre_topc(A_535)
      | ~ l1_pre_topc(B_534)
      | ~ v2_pre_topc(B_534)
      | v2_struct_0(B_534)
      | ~ m1_subset_1(C_536,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_535),u1_struct_0(B_534))))
      | ~ v1_funct_2(C_536,u1_struct_0(A_535),u1_struct_0(B_534))
      | ~ v1_funct_1(C_536)
      | ~ v2_funct_1(C_536)
      | k2_relset_1(u1_struct_0(A_535),u1_struct_0(B_534),C_536) != k2_struct_0(B_534)
      | ~ m1_subset_1(D_537,k1_zfmisc_1(u1_struct_0(A_535)))
      | ~ m1_subset_1(C_536,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_535),u1_struct_0(B_534))))
      | ~ v1_funct_2(C_536,u1_struct_0(A_535),u1_struct_0(B_534))
      | ~ v1_funct_1(C_536)
      | ~ l1_struct_0(B_534)
      | ~ l1_struct_0(A_535) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_6141])).

tff(c_6455,plain,(
    ! [A_576,B_577,C_578,D_579] :
      ( k7_relset_1(u1_struct_0(A_576),u1_struct_0(B_577),C_578,k2_pre_topc(A_576,D_579)) = k2_pre_topc(B_577,k7_relset_1(u1_struct_0(A_576),u1_struct_0(B_577),C_578,D_579))
      | ~ v2_funct_1(C_578)
      | k2_relset_1(u1_struct_0(A_576),u1_struct_0(B_577),C_578) != k2_struct_0(B_577)
      | ~ m1_subset_1(k2_pre_topc(A_576,D_579),k1_zfmisc_1(u1_struct_0(A_576)))
      | ~ m1_subset_1(C_578,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_576),u1_struct_0(B_577))))
      | ~ v1_funct_2(C_578,u1_struct_0(A_576),u1_struct_0(B_577))
      | ~ v1_funct_1(C_578)
      | ~ l1_struct_0(B_577)
      | ~ l1_struct_0(A_576)
      | ~ m1_subset_1(D_579,k1_zfmisc_1(u1_struct_0(A_576)))
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(A_576),u1_struct_0(B_577),C_578),B_577,A_576)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_576),u1_struct_0(B_577),C_578),u1_struct_0(B_577),u1_struct_0(A_576))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_576),u1_struct_0(B_577),C_578))
      | ~ l1_pre_topc(A_576)
      | ~ v2_pre_topc(A_576)
      | ~ l1_pre_topc(B_577)
      | ~ v2_pre_topc(B_577)
      | v2_struct_0(B_577)
      | ~ m1_subset_1(C_578,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_576),u1_struct_0(B_577))))
      | ~ v1_funct_2(C_578,u1_struct_0(A_576),u1_struct_0(B_577))
      | ~ v1_funct_1(C_578)
      | ~ v2_funct_1(C_578)
      | k2_relset_1(u1_struct_0(A_576),u1_struct_0(B_577),C_578) != k2_struct_0(B_577)
      | ~ m1_subset_1(D_579,k1_zfmisc_1(u1_struct_0(A_576)))
      | ~ m1_subset_1(C_578,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_576),u1_struct_0(B_577))))
      | ~ v1_funct_2(C_578,u1_struct_0(A_576),u1_struct_0(B_577))
      | ~ v1_funct_1(C_578)
      | ~ l1_struct_0(B_577)
      | ~ l1_struct_0(A_576) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6265,c_42])).

tff(c_6463,plain,(
    ! [A_580,B_581,C_582,B_583] :
      ( k7_relset_1(u1_struct_0(A_580),u1_struct_0(B_581),C_582,k2_pre_topc(A_580,B_583)) = k2_pre_topc(B_581,k7_relset_1(u1_struct_0(A_580),u1_struct_0(B_581),C_582,B_583))
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(A_580),u1_struct_0(B_581),C_582),B_581,A_580)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_580),u1_struct_0(B_581),C_582),u1_struct_0(B_581),u1_struct_0(A_580))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_580),u1_struct_0(B_581),C_582))
      | ~ v2_pre_topc(A_580)
      | ~ l1_pre_topc(B_581)
      | ~ v2_pre_topc(B_581)
      | v2_struct_0(B_581)
      | ~ v2_funct_1(C_582)
      | k2_relset_1(u1_struct_0(A_580),u1_struct_0(B_581),C_582) != k2_struct_0(B_581)
      | ~ m1_subset_1(C_582,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_580),u1_struct_0(B_581))))
      | ~ v1_funct_2(C_582,u1_struct_0(A_580),u1_struct_0(B_581))
      | ~ v1_funct_1(C_582)
      | ~ l1_struct_0(B_581)
      | ~ l1_struct_0(A_580)
      | ~ m1_subset_1(B_583,k1_zfmisc_1(u1_struct_0(A_580)))
      | ~ l1_pre_topc(A_580) ) ),
    inference(resolution,[status(thm)],[c_8,c_6455])).

tff(c_6468,plain,(
    ! [B_583] :
      ( k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_3',B_583)) = k2_pre_topc('#skF_4',k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',B_583))
      | ~ v3_tops_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
      | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ v2_funct_1('#skF_5')
      | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_3')
      | ~ m1_subset_1(B_583,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_5840,c_6463])).

tff(c_6472,plain,(
    ! [B_583] :
      ( k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_3',B_583)) = k2_pre_topc('#skF_4',k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',B_583))
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(B_583,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5953,c_5974,c_62,c_60,c_58,c_114,c_106,c_66,c_64,c_72,c_131,c_5929,c_6468])).

tff(c_6474,plain,(
    ! [B_584] :
      ( k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_3',B_584)) = k2_pre_topc('#skF_4',k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',B_584))
      | ~ m1_subset_1(B_584,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_6472])).

tff(c_76,plain,
    ( k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_3','#skF_6')) != k2_pre_topc('#skF_4',k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'))
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
    | k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_3')
    | ~ v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_5874,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_3','#skF_6')) != k2_pre_topc('#skF_4',k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5833,c_119,c_114,c_106,c_76])).

tff(c_6496,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6474,c_5874])).

tff(c_6523,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5831,c_6496])).

tff(c_6525,plain,(
    ~ v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_6527,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5832,c_6525])).

tff(c_6529,plain,(
    k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_6528,plain,(
    v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_6591,plain,(
    ! [A_605,B_606,C_607] :
      ( k1_relset_1(u1_struct_0(A_605),u1_struct_0(B_606),C_607) = k2_struct_0(A_605)
      | ~ v3_tops_2(C_607,A_605,B_606)
      | ~ m1_subset_1(C_607,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_605),u1_struct_0(B_606))))
      | ~ v1_funct_2(C_607,u1_struct_0(A_605),u1_struct_0(B_606))
      | ~ v1_funct_1(C_607)
      | ~ l1_pre_topc(B_606)
      | ~ l1_pre_topc(A_605) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6598,plain,
    ( k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_3')
    | ~ v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_6591])).

tff(c_6602,plain,(
    k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64,c_62,c_60,c_6528,c_6598])).

tff(c_6604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6529,c_6602])).

tff(c_6606,plain,(
    k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_6605,plain,(
    v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_6675,plain,(
    ! [A_628,B_629,C_630] :
      ( k2_relset_1(u1_struct_0(A_628),u1_struct_0(B_629),C_630) = k2_struct_0(B_629)
      | ~ v3_tops_2(C_630,A_628,B_629)
      | ~ m1_subset_1(C_630,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_628),u1_struct_0(B_629))))
      | ~ v1_funct_2(C_630,u1_struct_0(A_628),u1_struct_0(B_629))
      | ~ v1_funct_1(C_630)
      | ~ l1_pre_topc(B_629)
      | ~ l1_pre_topc(A_628) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6682,plain,
    ( k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4')
    | ~ v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_6675])).

tff(c_6686,plain,(
    k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64,c_62,c_60,c_6605,c_6682])).

tff(c_6688,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6606,c_6686])).

tff(c_6690,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_6689,plain,(
    v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_6722,plain,(
    ! [C_644,A_645,B_646] :
      ( v2_funct_1(C_644)
      | ~ v3_tops_2(C_644,A_645,B_646)
      | ~ m1_subset_1(C_644,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_645),u1_struct_0(B_646))))
      | ~ v1_funct_2(C_644,u1_struct_0(A_645),u1_struct_0(B_646))
      | ~ v1_funct_1(C_644)
      | ~ l1_pre_topc(B_646)
      | ~ l1_pre_topc(A_645) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6729,plain,
    ( v2_funct_1('#skF_5')
    | ~ v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_6722])).

tff(c_6733,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64,c_62,c_60,c_6689,c_6729])).

tff(c_6735,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6690,c_6733])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n010.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 10:44:29 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.27/4.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.27/4.13  
% 11.27/4.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.27/4.13  %$ v5_pre_topc > v3_tops_2 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v2_funct_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 11.27/4.13  
% 11.27/4.13  %Foreground sorts:
% 11.27/4.13  
% 11.27/4.13  
% 11.27/4.13  %Background operators:
% 11.27/4.13  
% 11.27/4.13  
% 11.27/4.13  %Foreground operators:
% 11.27/4.13  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.27/4.13  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.27/4.13  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.27/4.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.27/4.13  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.27/4.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.27/4.13  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 11.27/4.13  tff(v3_tops_2, type, v3_tops_2: ($i * $i * $i) > $o).
% 11.27/4.13  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.27/4.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.27/4.13  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 11.27/4.13  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 11.27/4.13  tff('#skF_5', type, '#skF_5': $i).
% 11.27/4.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.27/4.13  tff('#skF_6', type, '#skF_6': $i).
% 11.27/4.13  tff('#skF_3', type, '#skF_3': $i).
% 11.27/4.13  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.27/4.13  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.27/4.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.27/4.13  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.27/4.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.27/4.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.27/4.13  tff('#skF_4', type, '#skF_4': $i).
% 11.27/4.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.27/4.13  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 11.27/4.13  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.27/4.13  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.27/4.13  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 11.27/4.13  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 11.27/4.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.27/4.13  
% 11.43/4.17  tff(f_249, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> ((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_pre_topc(A, D)) = k2_pre_topc(B, k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_2)).
% 11.43/4.17  tff(f_103, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_pre_topc(A, D)), k2_pre_topc(B, k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_tops_2)).
% 11.43/4.17  tff(f_77, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 11.43/4.17  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 11.43/4.17  tff(f_144, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => v2_funct_1(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_tops_2)).
% 11.43/4.17  tff(f_126, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 11.43/4.17  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> (((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & v5_pre_topc(C, A, B)) & v5_pre_topc(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_2)).
% 11.43/4.17  tff(f_216, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> ((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_pre_topc(B, D)) = k2_pre_topc(A, k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_tops_2)).
% 11.43/4.17  tff(f_165, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => (k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k8_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tops_2)).
% 11.43/4.17  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 11.43/4.17  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.43/4.17  tff(f_184, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((~v2_struct_0(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) => v3_tops_2(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_tops_2)).
% 11.43/4.17  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_249])).
% 11.43/4.17  tff(c_98, plain, (v3_tops_2('#skF_5', '#skF_3', '#skF_4') | k1_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_249])).
% 11.43/4.17  tff(c_119, plain, (k1_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_98])).
% 11.43/4.17  tff(c_92, plain, (v3_tops_2('#skF_5', '#skF_3', '#skF_4') | k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_249])).
% 11.43/4.17  tff(c_114, plain, (k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_92])).
% 11.43/4.17  tff(c_86, plain, (v3_tops_2('#skF_5', '#skF_3', '#skF_4') | v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_249])).
% 11.43/4.17  tff(c_106, plain, (v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_86])).
% 11.43/4.17  tff(c_78, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_funct_1('#skF_5') | k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')!=k2_struct_0('#skF_4') | k1_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')!=k2_struct_0('#skF_3') | ~v3_tops_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_249])).
% 11.43/4.17  tff(c_133, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_tops_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_114, c_106, c_78])).
% 11.43/4.17  tff(c_134, plain, (~v3_tops_2('#skF_5', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_133])).
% 11.43/4.17  tff(c_70, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_249])).
% 11.43/4.17  tff(c_64, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_249])).
% 11.43/4.17  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_249])).
% 11.43/4.17  tff(c_60, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_249])).
% 11.43/4.17  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_249])).
% 11.43/4.17  tff(c_72, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_249])).
% 11.43/4.17  tff(c_66, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_249])).
% 11.43/4.17  tff(c_274, plain, (![A_158, B_159, C_160]: (m1_subset_1('#skF_1'(A_158, B_159, C_160), k1_zfmisc_1(u1_struct_0(A_158))) | v5_pre_topc(C_160, A_158, B_159) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_158), u1_struct_0(B_159)))) | ~v1_funct_2(C_160, u1_struct_0(A_158), u1_struct_0(B_159)) | ~v1_funct_1(C_160) | ~l1_pre_topc(B_159) | ~v2_pre_topc(B_159) | v2_struct_0(B_159) | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.43/4.17  tff(c_279, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v5_pre_topc('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_58, c_274])).
% 11.43/4.17  tff(c_283, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v5_pre_topc('#skF_5', '#skF_3', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_62, c_60, c_279])).
% 11.43/4.17  tff(c_284, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v5_pre_topc('#skF_5', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_283])).
% 11.43/4.17  tff(c_285, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_284])).
% 11.43/4.17  tff(c_24, plain, (![A_13, B_14, C_15]: (m1_subset_1(k2_tops_2(A_13, B_14, C_15), k1_zfmisc_1(k2_zfmisc_1(B_14, A_13))) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_2(C_15, A_13, B_14) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.43/4.17  tff(c_10, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.43/4.17  tff(c_240, plain, (![A_155, B_156, C_157]: (v2_funct_1(k2_tops_2(u1_struct_0(A_155), u1_struct_0(B_156), C_157)) | ~v2_funct_1(C_157) | k2_relset_1(u1_struct_0(A_155), u1_struct_0(B_156), C_157)!=k2_struct_0(B_156) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_155), u1_struct_0(B_156)))) | ~v1_funct_2(C_157, u1_struct_0(A_155), u1_struct_0(B_156)) | ~v1_funct_1(C_157) | ~l1_struct_0(B_156) | ~l1_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.43/4.17  tff(c_247, plain, (v2_funct_1(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')) | ~v2_funct_1('#skF_5') | k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')!=k2_struct_0('#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_240])).
% 11.43/4.17  tff(c_251, plain, (v2_funct_1(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')) | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_114, c_106, c_247])).
% 11.43/4.17  tff(c_252, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_251])).
% 11.43/4.17  tff(c_255, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_10, c_252])).
% 11.43/4.17  tff(c_259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_255])).
% 11.43/4.17  tff(c_261, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_251])).
% 11.43/4.17  tff(c_260, plain, (~l1_struct_0('#skF_4') | v2_funct_1(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))), inference(splitRight, [status(thm)], [c_251])).
% 11.43/4.17  tff(c_264, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_260])).
% 11.43/4.17  tff(c_267, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_10, c_264])).
% 11.43/4.17  tff(c_271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_267])).
% 11.43/4.17  tff(c_273, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_260])).
% 11.43/4.17  tff(c_38, plain, (![B_42, A_38, C_44]: (k1_relset_1(u1_struct_0(B_42), u1_struct_0(A_38), k2_tops_2(u1_struct_0(A_38), u1_struct_0(B_42), C_44))=k2_struct_0(B_42) | ~v2_funct_1(C_44) | k2_relset_1(u1_struct_0(A_38), u1_struct_0(B_42), C_44)!=k2_struct_0(B_42) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_38), u1_struct_0(B_42)))) | ~v1_funct_2(C_44, u1_struct_0(A_38), u1_struct_0(B_42)) | ~v1_funct_1(C_44) | ~l1_struct_0(B_42) | v2_struct_0(B_42) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_126])).
% 11.43/4.17  tff(c_36, plain, (![B_42, A_38, C_44]: (k2_relset_1(u1_struct_0(B_42), u1_struct_0(A_38), k2_tops_2(u1_struct_0(A_38), u1_struct_0(B_42), C_44))=k2_struct_0(A_38) | ~v2_funct_1(C_44) | k2_relset_1(u1_struct_0(A_38), u1_struct_0(B_42), C_44)!=k2_struct_0(B_42) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_38), u1_struct_0(B_42)))) | ~v1_funct_2(C_44, u1_struct_0(A_38), u1_struct_0(B_42)) | ~v1_funct_1(C_44) | ~l1_struct_0(B_42) | v2_struct_0(B_42) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_126])).
% 11.43/4.17  tff(c_125, plain, (![A_121, B_122, C_123]: (v1_funct_1(k2_tops_2(A_121, B_122, C_123)) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~v1_funct_2(C_123, A_121, B_122) | ~v1_funct_1(C_123))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.43/4.17  tff(c_128, plain, (v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_125])).
% 11.43/4.17  tff(c_131, plain, (v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_128])).
% 11.43/4.17  tff(c_135, plain, (![A_124, B_125, C_126]: (v1_funct_2(k2_tops_2(A_124, B_125, C_126), B_125, A_124) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~v1_funct_2(C_126, A_124, B_125) | ~v1_funct_1(C_126))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.43/4.17  tff(c_137, plain, (v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_135])).
% 11.43/4.17  tff(c_140, plain, (v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_137])).
% 11.43/4.17  tff(c_171, plain, (![C_134, A_135, B_136]: (v5_pre_topc(C_134, A_135, B_136) | ~v3_tops_2(C_134, A_135, B_136) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_135), u1_struct_0(B_136)))) | ~v1_funct_2(C_134, u1_struct_0(A_135), u1_struct_0(B_136)) | ~v1_funct_1(C_134) | ~l1_pre_topc(B_136) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.43/4.17  tff(c_425, plain, (![B_201, A_202, C_203]: (v5_pre_topc(k2_tops_2(u1_struct_0(B_201), u1_struct_0(A_202), C_203), A_202, B_201) | ~v3_tops_2(k2_tops_2(u1_struct_0(B_201), u1_struct_0(A_202), C_203), A_202, B_201) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_201), u1_struct_0(A_202), C_203), u1_struct_0(A_202), u1_struct_0(B_201)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_201), u1_struct_0(A_202), C_203)) | ~l1_pre_topc(B_201) | ~l1_pre_topc(A_202) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_201), u1_struct_0(A_202)))) | ~v1_funct_2(C_203, u1_struct_0(B_201), u1_struct_0(A_202)) | ~v1_funct_1(C_203))), inference(resolution, [status(thm)], [c_24, c_171])).
% 11.43/4.17  tff(c_432, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), '#skF_4', '#skF_3') | ~v3_tops_2(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_140, c_425])).
% 11.43/4.17  tff(c_436, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), '#skF_4', '#skF_3') | ~v3_tops_2(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_64, c_70, c_131, c_432])).
% 11.43/4.17  tff(c_437, plain, (~v3_tops_2(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), '#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_436])).
% 11.43/4.17  tff(c_272, plain, (v2_funct_1(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))), inference(splitRight, [status(thm)], [c_260])).
% 11.43/4.17  tff(c_406, plain, (![A_195, B_196, C_197]: (m1_subset_1('#skF_2'(A_195, B_196, C_197), k1_zfmisc_1(u1_struct_0(B_196))) | v3_tops_2(C_197, A_195, B_196) | ~v2_funct_1(C_197) | k2_relset_1(u1_struct_0(A_195), u1_struct_0(B_196), C_197)!=k2_struct_0(B_196) | k1_relset_1(u1_struct_0(A_195), u1_struct_0(B_196), C_197)!=k2_struct_0(A_195) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_195), u1_struct_0(B_196)))) | ~v1_funct_2(C_197, u1_struct_0(A_195), u1_struct_0(B_196)) | ~v1_funct_1(C_197) | ~l1_pre_topc(B_196) | ~v2_pre_topc(B_196) | ~l1_pre_topc(A_195) | ~v2_pre_topc(A_195) | v2_struct_0(A_195))), inference(cnfTransformation, [status(thm)], [f_216])).
% 11.43/4.17  tff(c_412, plain, (![A_195, B_196, C_15]: (m1_subset_1('#skF_2'(A_195, B_196, k2_tops_2(u1_struct_0(B_196), u1_struct_0(A_195), C_15)), k1_zfmisc_1(u1_struct_0(B_196))) | v3_tops_2(k2_tops_2(u1_struct_0(B_196), u1_struct_0(A_195), C_15), A_195, B_196) | ~v2_funct_1(k2_tops_2(u1_struct_0(B_196), u1_struct_0(A_195), C_15)) | k2_relset_1(u1_struct_0(A_195), u1_struct_0(B_196), k2_tops_2(u1_struct_0(B_196), u1_struct_0(A_195), C_15))!=k2_struct_0(B_196) | k1_relset_1(u1_struct_0(A_195), u1_struct_0(B_196), k2_tops_2(u1_struct_0(B_196), u1_struct_0(A_195), C_15))!=k2_struct_0(A_195) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_196), u1_struct_0(A_195), C_15), u1_struct_0(A_195), u1_struct_0(B_196)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_196), u1_struct_0(A_195), C_15)) | ~l1_pre_topc(B_196) | ~v2_pre_topc(B_196) | ~l1_pre_topc(A_195) | ~v2_pre_topc(A_195) | v2_struct_0(A_195) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_196), u1_struct_0(A_195)))) | ~v1_funct_2(C_15, u1_struct_0(B_196), u1_struct_0(A_195)) | ~v1_funct_1(C_15))), inference(resolution, [status(thm)], [c_24, c_406])).
% 11.43/4.17  tff(c_80, plain, (![D_114]: (v3_tops_2('#skF_5', '#skF_3', '#skF_4') | k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_3', D_114))=k2_pre_topc('#skF_4', k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', D_114)) | ~m1_subset_1(D_114, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_249])).
% 11.43/4.17  tff(c_161, plain, (![D_114]: (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_3', D_114))=k2_pre_topc('#skF_4', k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', D_114)) | ~m1_subset_1(D_114, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_134, c_80])).
% 11.43/4.17  tff(c_42, plain, (![B_60, A_52, C_64, D_66]: (k8_relset_1(u1_struct_0(B_60), u1_struct_0(A_52), k2_tops_2(u1_struct_0(A_52), u1_struct_0(B_60), C_64), D_66)=k7_relset_1(u1_struct_0(A_52), u1_struct_0(B_60), C_64, D_66) | ~v2_funct_1(C_64) | k2_relset_1(u1_struct_0(A_52), u1_struct_0(B_60), C_64)!=k2_struct_0(B_60) | ~m1_subset_1(D_66, k1_zfmisc_1(u1_struct_0(A_52))) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_52), u1_struct_0(B_60)))) | ~v1_funct_2(C_64, u1_struct_0(A_52), u1_struct_0(B_60)) | ~v1_funct_1(C_64) | ~l1_struct_0(B_60) | ~l1_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_165])).
% 11.43/4.17  tff(c_418, plain, (![A_198, B_199, C_200]: (k8_relset_1(u1_struct_0(A_198), u1_struct_0(B_199), C_200, k2_pre_topc(B_199, '#skF_2'(A_198, B_199, C_200)))!=k2_pre_topc(A_198, k8_relset_1(u1_struct_0(A_198), u1_struct_0(B_199), C_200, '#skF_2'(A_198, B_199, C_200))) | v3_tops_2(C_200, A_198, B_199) | ~v2_funct_1(C_200) | k2_relset_1(u1_struct_0(A_198), u1_struct_0(B_199), C_200)!=k2_struct_0(B_199) | k1_relset_1(u1_struct_0(A_198), u1_struct_0(B_199), C_200)!=k2_struct_0(A_198) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_198), u1_struct_0(B_199)))) | ~v1_funct_2(C_200, u1_struct_0(A_198), u1_struct_0(B_199)) | ~v1_funct_1(C_200) | ~l1_pre_topc(B_199) | ~v2_pre_topc(B_199) | ~l1_pre_topc(A_198) | ~v2_pre_topc(A_198) | v2_struct_0(A_198))), inference(cnfTransformation, [status(thm)], [f_216])).
% 11.43/4.17  tff(c_1403, plain, (![B_258, A_259, C_260]: (k8_relset_1(u1_struct_0(B_258), u1_struct_0(A_259), k2_tops_2(u1_struct_0(A_259), u1_struct_0(B_258), C_260), k2_pre_topc(A_259, '#skF_2'(B_258, A_259, k2_tops_2(u1_struct_0(A_259), u1_struct_0(B_258), C_260))))!=k2_pre_topc(B_258, k7_relset_1(u1_struct_0(A_259), u1_struct_0(B_258), C_260, '#skF_2'(B_258, A_259, k2_tops_2(u1_struct_0(A_259), u1_struct_0(B_258), C_260)))) | v3_tops_2(k2_tops_2(u1_struct_0(A_259), u1_struct_0(B_258), C_260), B_258, A_259) | ~v2_funct_1(k2_tops_2(u1_struct_0(A_259), u1_struct_0(B_258), C_260)) | k2_relset_1(u1_struct_0(B_258), u1_struct_0(A_259), k2_tops_2(u1_struct_0(A_259), u1_struct_0(B_258), C_260))!=k2_struct_0(A_259) | k1_relset_1(u1_struct_0(B_258), u1_struct_0(A_259), k2_tops_2(u1_struct_0(A_259), u1_struct_0(B_258), C_260))!=k2_struct_0(B_258) | ~m1_subset_1(k2_tops_2(u1_struct_0(A_259), u1_struct_0(B_258), C_260), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_258), u1_struct_0(A_259)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_259), u1_struct_0(B_258), C_260), u1_struct_0(B_258), u1_struct_0(A_259)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_259), u1_struct_0(B_258), C_260)) | ~l1_pre_topc(A_259) | ~v2_pre_topc(A_259) | ~l1_pre_topc(B_258) | ~v2_pre_topc(B_258) | v2_struct_0(B_258) | ~v2_funct_1(C_260) | k2_relset_1(u1_struct_0(A_259), u1_struct_0(B_258), C_260)!=k2_struct_0(B_258) | ~m1_subset_1('#skF_2'(B_258, A_259, k2_tops_2(u1_struct_0(A_259), u1_struct_0(B_258), C_260)), k1_zfmisc_1(u1_struct_0(A_259))) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_259), u1_struct_0(B_258)))) | ~v1_funct_2(C_260, u1_struct_0(A_259), u1_struct_0(B_258)) | ~v1_funct_1(C_260) | ~l1_struct_0(B_258) | ~l1_struct_0(A_259))), inference(superposition, [status(thm), theory('equality')], [c_42, c_418])).
% 11.43/4.17  tff(c_5525, plain, (![A_366, B_367, C_368]: (k7_relset_1(u1_struct_0(A_366), u1_struct_0(B_367), C_368, k2_pre_topc(A_366, '#skF_2'(B_367, A_366, k2_tops_2(u1_struct_0(A_366), u1_struct_0(B_367), C_368))))!=k2_pre_topc(B_367, k7_relset_1(u1_struct_0(A_366), u1_struct_0(B_367), C_368, '#skF_2'(B_367, A_366, k2_tops_2(u1_struct_0(A_366), u1_struct_0(B_367), C_368)))) | v3_tops_2(k2_tops_2(u1_struct_0(A_366), u1_struct_0(B_367), C_368), B_367, A_366) | ~v2_funct_1(k2_tops_2(u1_struct_0(A_366), u1_struct_0(B_367), C_368)) | k2_relset_1(u1_struct_0(B_367), u1_struct_0(A_366), k2_tops_2(u1_struct_0(A_366), u1_struct_0(B_367), C_368))!=k2_struct_0(A_366) | k1_relset_1(u1_struct_0(B_367), u1_struct_0(A_366), k2_tops_2(u1_struct_0(A_366), u1_struct_0(B_367), C_368))!=k2_struct_0(B_367) | ~m1_subset_1(k2_tops_2(u1_struct_0(A_366), u1_struct_0(B_367), C_368), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_367), u1_struct_0(A_366)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_366), u1_struct_0(B_367), C_368), u1_struct_0(B_367), u1_struct_0(A_366)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_366), u1_struct_0(B_367), C_368)) | ~l1_pre_topc(A_366) | ~v2_pre_topc(A_366) | ~l1_pre_topc(B_367) | ~v2_pre_topc(B_367) | v2_struct_0(B_367) | ~v2_funct_1(C_368) | k2_relset_1(u1_struct_0(A_366), u1_struct_0(B_367), C_368)!=k2_struct_0(B_367) | ~m1_subset_1('#skF_2'(B_367, A_366, k2_tops_2(u1_struct_0(A_366), u1_struct_0(B_367), C_368)), k1_zfmisc_1(u1_struct_0(A_366))) | ~m1_subset_1(C_368, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_366), u1_struct_0(B_367)))) | ~v1_funct_2(C_368, u1_struct_0(A_366), u1_struct_0(B_367)) | ~v1_funct_1(C_368) | ~l1_struct_0(B_367) | ~l1_struct_0(A_366) | ~v2_funct_1(C_368) | k2_relset_1(u1_struct_0(A_366), u1_struct_0(B_367), C_368)!=k2_struct_0(B_367) | ~m1_subset_1(k2_pre_topc(A_366, '#skF_2'(B_367, A_366, k2_tops_2(u1_struct_0(A_366), u1_struct_0(B_367), C_368))), k1_zfmisc_1(u1_struct_0(A_366))) | ~m1_subset_1(C_368, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_366), u1_struct_0(B_367)))) | ~v1_funct_2(C_368, u1_struct_0(A_366), u1_struct_0(B_367)) | ~v1_funct_1(C_368) | ~l1_struct_0(B_367) | ~l1_struct_0(A_366))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1403])).
% 11.43/4.17  tff(c_5528, plain, (v3_tops_2(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), '#skF_4', '#skF_3') | ~v2_funct_1(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')) | k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_3') | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4') | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~v2_funct_1('#skF_5') | k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')!=k2_struct_0('#skF_4') | ~m1_subset_1(k2_pre_topc('#skF_3', '#skF_2'('#skF_4', '#skF_3', k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_3', k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_161, c_5525])).
% 11.43/4.17  tff(c_5531, plain, (v3_tops_2(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), '#skF_4', '#skF_3') | k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_3') | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4') | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | v2_struct_0('#skF_4') | ~m1_subset_1(k2_pre_topc('#skF_3', '#skF_2'('#skF_4', '#skF_3', k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_2'('#skF_4', '#skF_3', k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_261, c_273, c_62, c_60, c_58, c_114, c_106, c_66, c_64, c_72, c_70, c_131, c_140, c_272, c_5528])).
% 11.43/4.17  tff(c_5532, plain, (k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_3') | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4') | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~m1_subset_1(k2_pre_topc('#skF_3', '#skF_2'('#skF_4', '#skF_3', k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_2'('#skF_4', '#skF_3', k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_68, c_437, c_5531])).
% 11.43/4.17  tff(c_5533, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_3', k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_5532])).
% 11.43/4.17  tff(c_5536, plain, (v3_tops_2(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), '#skF_4', '#skF_3') | ~v2_funct_1(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')) | k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_3') | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4') | ~v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_412, c_5533])).
% 11.43/4.17  tff(c_5539, plain, (v3_tops_2(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), '#skF_4', '#skF_3') | k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_3') | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_66, c_64, c_72, c_70, c_131, c_140, c_272, c_5536])).
% 11.43/4.17  tff(c_5540, plain, (k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_3') | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_437, c_5539])).
% 11.43/4.17  tff(c_5541, plain, (k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_5540])).
% 11.43/4.17  tff(c_5544, plain, (~v2_funct_1('#skF_5') | k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')!=k2_struct_0('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_5541])).
% 11.43/4.17  tff(c_5547, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_261, c_273, c_62, c_60, c_58, c_114, c_106, c_5544])).
% 11.43/4.17  tff(c_5549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_5547])).
% 11.43/4.17  tff(c_5550, plain, (k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_5540])).
% 11.43/4.17  tff(c_5572, plain, (~v2_funct_1('#skF_5') | k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')!=k2_struct_0('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_5550])).
% 11.43/4.17  tff(c_5575, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_261, c_273, c_62, c_60, c_58, c_114, c_106, c_5572])).
% 11.43/4.17  tff(c_5577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_5575])).
% 11.43/4.17  tff(c_5579, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_3', k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_5532])).
% 11.43/4.17  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k2_pre_topc(A_3, B_4), k1_zfmisc_1(u1_struct_0(A_3))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.43/4.17  tff(c_5578, plain, (~m1_subset_1(k2_pre_topc('#skF_3', '#skF_2'('#skF_4', '#skF_3', k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4') | k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_5532])).
% 11.43/4.17  tff(c_5580, plain, (k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_5578])).
% 11.43/4.17  tff(c_5583, plain, (~v2_funct_1('#skF_5') | k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')!=k2_struct_0('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_5580])).
% 11.43/4.17  tff(c_5586, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_261, c_273, c_62, c_60, c_58, c_114, c_106, c_5583])).
% 11.43/4.17  tff(c_5588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_5586])).
% 11.43/4.17  tff(c_5589, plain, (k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4') | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~m1_subset_1(k2_pre_topc('#skF_3', '#skF_2'('#skF_4', '#skF_3', k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_5578])).
% 11.43/4.17  tff(c_5609, plain, (~m1_subset_1(k2_pre_topc('#skF_3', '#skF_2'('#skF_4', '#skF_3', k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_5589])).
% 11.43/4.17  tff(c_5612, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_3', k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8, c_5609])).
% 11.43/4.17  tff(c_5616, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_5579, c_5612])).
% 11.43/4.17  tff(c_5617, plain, (~m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_5589])).
% 11.43/4.17  tff(c_5689, plain, (k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_5617])).
% 11.43/4.17  tff(c_5692, plain, (~v2_funct_1('#skF_5') | k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')!=k2_struct_0('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_5689])).
% 11.43/4.17  tff(c_5695, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_261, c_273, c_62, c_60, c_58, c_114, c_106, c_5692])).
% 11.43/4.17  tff(c_5697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_5695])).
% 11.43/4.17  tff(c_5698, plain, (~m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_5617])).
% 11.43/4.17  tff(c_5720, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_24, c_5698])).
% 11.43/4.17  tff(c_5724, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_5720])).
% 11.43/4.17  tff(c_5725, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_436])).
% 11.43/4.17  tff(c_12, plain, (![C_12, A_6, B_10]: (v3_tops_2(C_12, A_6, B_10) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_6), u1_struct_0(B_10), C_12), B_10, A_6) | ~v5_pre_topc(C_12, A_6, B_10) | ~v2_funct_1(C_12) | k2_relset_1(u1_struct_0(A_6), u1_struct_0(B_10), C_12)!=k2_struct_0(B_10) | k1_relset_1(u1_struct_0(A_6), u1_struct_0(B_10), C_12)!=k2_struct_0(A_6) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6), u1_struct_0(B_10)))) | ~v1_funct_2(C_12, u1_struct_0(A_6), u1_struct_0(B_10)) | ~v1_funct_1(C_12) | ~l1_pre_topc(B_10) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.43/4.17  tff(c_5740, plain, (v3_tops_2('#skF_5', '#skF_3', '#skF_4') | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_4') | ~v2_funct_1('#skF_5') | k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')!=k2_struct_0('#skF_4') | k1_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')!=k2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_5725, c_12])).
% 11.43/4.17  tff(c_5743, plain, (v3_tops_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_64, c_62, c_60, c_58, c_119, c_114, c_106, c_285, c_5740])).
% 11.43/4.17  tff(c_5745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_5743])).
% 11.43/4.17  tff(c_5747, plain, (~v5_pre_topc('#skF_5', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_284])).
% 11.43/4.17  tff(c_5746, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_284])).
% 11.43/4.17  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.43/4.17  tff(c_5817, plain, (![A_402, B_403, C_404]: (~r1_tarski(k7_relset_1(u1_struct_0(A_402), u1_struct_0(B_403), C_404, k2_pre_topc(A_402, '#skF_1'(A_402, B_403, C_404))), k2_pre_topc(B_403, k7_relset_1(u1_struct_0(A_402), u1_struct_0(B_403), C_404, '#skF_1'(A_402, B_403, C_404)))) | v5_pre_topc(C_404, A_402, B_403) | ~m1_subset_1(C_404, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_402), u1_struct_0(B_403)))) | ~v1_funct_2(C_404, u1_struct_0(A_402), u1_struct_0(B_403)) | ~v1_funct_1(C_404) | ~l1_pre_topc(B_403) | ~v2_pre_topc(B_403) | v2_struct_0(B_403) | ~l1_pre_topc(A_402) | ~v2_pre_topc(A_402))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.43/4.17  tff(c_5825, plain, (~r1_tarski(k2_pre_topc('#skF_4', k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), k2_pre_topc('#skF_4', k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')))) | v5_pre_topc('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_161, c_5817])).
% 11.43/4.17  tff(c_5828, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5746, c_72, c_70, c_66, c_64, c_62, c_60, c_58, c_6, c_5825])).
% 11.43/4.17  tff(c_5830, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_5747, c_5828])).
% 11.43/4.17  tff(c_5832, plain, (v3_tops_2('#skF_5', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_133])).
% 11.43/4.17  tff(c_5831, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_133])).
% 11.43/4.17  tff(c_5932, plain, (![A_435, B_436, C_437]: (v2_funct_1(k2_tops_2(u1_struct_0(A_435), u1_struct_0(B_436), C_437)) | ~v2_funct_1(C_437) | k2_relset_1(u1_struct_0(A_435), u1_struct_0(B_436), C_437)!=k2_struct_0(B_436) | ~m1_subset_1(C_437, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_435), u1_struct_0(B_436)))) | ~v1_funct_2(C_437, u1_struct_0(A_435), u1_struct_0(B_436)) | ~v1_funct_1(C_437) | ~l1_struct_0(B_436) | ~l1_struct_0(A_435))), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.43/4.17  tff(c_5939, plain, (v2_funct_1(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')) | ~v2_funct_1('#skF_5') | k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')!=k2_struct_0('#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_5932])).
% 11.43/4.17  tff(c_5943, plain, (v2_funct_1(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')) | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_114, c_106, c_5939])).
% 11.43/4.17  tff(c_5944, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_5943])).
% 11.43/4.17  tff(c_5947, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_10, c_5944])).
% 11.43/4.17  tff(c_5951, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_5947])).
% 11.43/4.17  tff(c_5953, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_5943])).
% 11.43/4.17  tff(c_5952, plain, (~l1_struct_0('#skF_4') | v2_funct_1(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))), inference(splitRight, [status(thm)], [c_5943])).
% 11.43/4.17  tff(c_5965, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_5952])).
% 11.43/4.17  tff(c_5968, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_10, c_5965])).
% 11.43/4.17  tff(c_5972, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_5968])).
% 11.43/4.17  tff(c_5974, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_5952])).
% 11.43/4.17  tff(c_5833, plain, (v3_tops_2('#skF_5', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_80])).
% 11.43/4.17  tff(c_5919, plain, (![A_432, B_433, C_434]: (v3_tops_2(k2_tops_2(u1_struct_0(A_432), u1_struct_0(B_433), C_434), B_433, A_432) | ~v3_tops_2(C_434, A_432, B_433) | ~m1_subset_1(C_434, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_432), u1_struct_0(B_433)))) | ~v1_funct_2(C_434, u1_struct_0(A_432), u1_struct_0(B_433)) | ~v1_funct_1(C_434) | ~l1_pre_topc(B_433) | v2_struct_0(B_433) | ~l1_pre_topc(A_432))), inference(cnfTransformation, [status(thm)], [f_184])).
% 11.43/4.17  tff(c_5924, plain, (v3_tops_2(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), '#skF_4', '#skF_3') | ~v3_tops_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_58, c_5919])).
% 11.43/4.17  tff(c_5928, plain, (v3_tops_2(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), '#skF_4', '#skF_3') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_64, c_62, c_60, c_5833, c_5924])).
% 11.43/4.17  tff(c_5929, plain, (v3_tops_2(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), '#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_5928])).
% 11.43/4.17  tff(c_5835, plain, (![A_405, B_406, C_407]: (v1_funct_2(k2_tops_2(A_405, B_406, C_407), B_406, A_405) | ~m1_subset_1(C_407, k1_zfmisc_1(k2_zfmisc_1(A_405, B_406))) | ~v1_funct_2(C_407, A_405, B_406) | ~v1_funct_1(C_407))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.43/4.17  tff(c_5837, plain, (v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_5835])).
% 11.43/4.17  tff(c_5840, plain, (v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_5837])).
% 11.43/4.17  tff(c_5995, plain, (![A_447, B_448, C_449, D_450]: (k8_relset_1(u1_struct_0(A_447), u1_struct_0(B_448), C_449, k2_pre_topc(B_448, D_450))=k2_pre_topc(A_447, k8_relset_1(u1_struct_0(A_447), u1_struct_0(B_448), C_449, D_450)) | ~m1_subset_1(D_450, k1_zfmisc_1(u1_struct_0(B_448))) | ~v3_tops_2(C_449, A_447, B_448) | ~m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_447), u1_struct_0(B_448)))) | ~v1_funct_2(C_449, u1_struct_0(A_447), u1_struct_0(B_448)) | ~v1_funct_1(C_449) | ~l1_pre_topc(B_448) | ~v2_pre_topc(B_448) | ~l1_pre_topc(A_447) | ~v2_pre_topc(A_447) | v2_struct_0(A_447))), inference(cnfTransformation, [status(thm)], [f_216])).
% 11.43/4.17  tff(c_6141, plain, (![A_502, B_503, C_504, D_505]: (k8_relset_1(u1_struct_0(A_502), u1_struct_0(B_503), k2_tops_2(u1_struct_0(B_503), u1_struct_0(A_502), C_504), k2_pre_topc(B_503, D_505))=k2_pre_topc(A_502, k8_relset_1(u1_struct_0(A_502), u1_struct_0(B_503), k2_tops_2(u1_struct_0(B_503), u1_struct_0(A_502), C_504), D_505)) | ~m1_subset_1(D_505, k1_zfmisc_1(u1_struct_0(B_503))) | ~v3_tops_2(k2_tops_2(u1_struct_0(B_503), u1_struct_0(A_502), C_504), A_502, B_503) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_503), u1_struct_0(A_502), C_504), u1_struct_0(A_502), u1_struct_0(B_503)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_503), u1_struct_0(A_502), C_504)) | ~l1_pre_topc(B_503) | ~v2_pre_topc(B_503) | ~l1_pre_topc(A_502) | ~v2_pre_topc(A_502) | v2_struct_0(A_502) | ~m1_subset_1(C_504, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_503), u1_struct_0(A_502)))) | ~v1_funct_2(C_504, u1_struct_0(B_503), u1_struct_0(A_502)) | ~v1_funct_1(C_504))), inference(resolution, [status(thm)], [c_24, c_5995])).
% 11.43/4.17  tff(c_6265, plain, (![B_534, A_535, C_536, D_537]: (k8_relset_1(u1_struct_0(B_534), u1_struct_0(A_535), k2_tops_2(u1_struct_0(A_535), u1_struct_0(B_534), C_536), k2_pre_topc(A_535, D_537))=k2_pre_topc(B_534, k7_relset_1(u1_struct_0(A_535), u1_struct_0(B_534), C_536, D_537)) | ~m1_subset_1(D_537, k1_zfmisc_1(u1_struct_0(A_535))) | ~v3_tops_2(k2_tops_2(u1_struct_0(A_535), u1_struct_0(B_534), C_536), B_534, A_535) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_535), u1_struct_0(B_534), C_536), u1_struct_0(B_534), u1_struct_0(A_535)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_535), u1_struct_0(B_534), C_536)) | ~l1_pre_topc(A_535) | ~v2_pre_topc(A_535) | ~l1_pre_topc(B_534) | ~v2_pre_topc(B_534) | v2_struct_0(B_534) | ~m1_subset_1(C_536, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_535), u1_struct_0(B_534)))) | ~v1_funct_2(C_536, u1_struct_0(A_535), u1_struct_0(B_534)) | ~v1_funct_1(C_536) | ~v2_funct_1(C_536) | k2_relset_1(u1_struct_0(A_535), u1_struct_0(B_534), C_536)!=k2_struct_0(B_534) | ~m1_subset_1(D_537, k1_zfmisc_1(u1_struct_0(A_535))) | ~m1_subset_1(C_536, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_535), u1_struct_0(B_534)))) | ~v1_funct_2(C_536, u1_struct_0(A_535), u1_struct_0(B_534)) | ~v1_funct_1(C_536) | ~l1_struct_0(B_534) | ~l1_struct_0(A_535))), inference(superposition, [status(thm), theory('equality')], [c_42, c_6141])).
% 11.43/4.17  tff(c_6455, plain, (![A_576, B_577, C_578, D_579]: (k7_relset_1(u1_struct_0(A_576), u1_struct_0(B_577), C_578, k2_pre_topc(A_576, D_579))=k2_pre_topc(B_577, k7_relset_1(u1_struct_0(A_576), u1_struct_0(B_577), C_578, D_579)) | ~v2_funct_1(C_578) | k2_relset_1(u1_struct_0(A_576), u1_struct_0(B_577), C_578)!=k2_struct_0(B_577) | ~m1_subset_1(k2_pre_topc(A_576, D_579), k1_zfmisc_1(u1_struct_0(A_576))) | ~m1_subset_1(C_578, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_576), u1_struct_0(B_577)))) | ~v1_funct_2(C_578, u1_struct_0(A_576), u1_struct_0(B_577)) | ~v1_funct_1(C_578) | ~l1_struct_0(B_577) | ~l1_struct_0(A_576) | ~m1_subset_1(D_579, k1_zfmisc_1(u1_struct_0(A_576))) | ~v3_tops_2(k2_tops_2(u1_struct_0(A_576), u1_struct_0(B_577), C_578), B_577, A_576) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_576), u1_struct_0(B_577), C_578), u1_struct_0(B_577), u1_struct_0(A_576)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_576), u1_struct_0(B_577), C_578)) | ~l1_pre_topc(A_576) | ~v2_pre_topc(A_576) | ~l1_pre_topc(B_577) | ~v2_pre_topc(B_577) | v2_struct_0(B_577) | ~m1_subset_1(C_578, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_576), u1_struct_0(B_577)))) | ~v1_funct_2(C_578, u1_struct_0(A_576), u1_struct_0(B_577)) | ~v1_funct_1(C_578) | ~v2_funct_1(C_578) | k2_relset_1(u1_struct_0(A_576), u1_struct_0(B_577), C_578)!=k2_struct_0(B_577) | ~m1_subset_1(D_579, k1_zfmisc_1(u1_struct_0(A_576))) | ~m1_subset_1(C_578, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_576), u1_struct_0(B_577)))) | ~v1_funct_2(C_578, u1_struct_0(A_576), u1_struct_0(B_577)) | ~v1_funct_1(C_578) | ~l1_struct_0(B_577) | ~l1_struct_0(A_576))), inference(superposition, [status(thm), theory('equality')], [c_6265, c_42])).
% 11.43/4.17  tff(c_6463, plain, (![A_580, B_581, C_582, B_583]: (k7_relset_1(u1_struct_0(A_580), u1_struct_0(B_581), C_582, k2_pre_topc(A_580, B_583))=k2_pre_topc(B_581, k7_relset_1(u1_struct_0(A_580), u1_struct_0(B_581), C_582, B_583)) | ~v3_tops_2(k2_tops_2(u1_struct_0(A_580), u1_struct_0(B_581), C_582), B_581, A_580) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_580), u1_struct_0(B_581), C_582), u1_struct_0(B_581), u1_struct_0(A_580)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_580), u1_struct_0(B_581), C_582)) | ~v2_pre_topc(A_580) | ~l1_pre_topc(B_581) | ~v2_pre_topc(B_581) | v2_struct_0(B_581) | ~v2_funct_1(C_582) | k2_relset_1(u1_struct_0(A_580), u1_struct_0(B_581), C_582)!=k2_struct_0(B_581) | ~m1_subset_1(C_582, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_580), u1_struct_0(B_581)))) | ~v1_funct_2(C_582, u1_struct_0(A_580), u1_struct_0(B_581)) | ~v1_funct_1(C_582) | ~l1_struct_0(B_581) | ~l1_struct_0(A_580) | ~m1_subset_1(B_583, k1_zfmisc_1(u1_struct_0(A_580))) | ~l1_pre_topc(A_580))), inference(resolution, [status(thm)], [c_8, c_6455])).
% 11.43/4.17  tff(c_6468, plain, (![B_583]: (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_3', B_583))=k2_pre_topc('#skF_4', k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', B_583)) | ~v3_tops_2(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')) | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~v2_funct_1('#skF_5') | k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')!=k2_struct_0('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3') | ~m1_subset_1(B_583, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_5840, c_6463])).
% 11.43/4.17  tff(c_6472, plain, (![B_583]: (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_3', B_583))=k2_pre_topc('#skF_4', k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', B_583)) | v2_struct_0('#skF_4') | ~m1_subset_1(B_583, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5953, c_5974, c_62, c_60, c_58, c_114, c_106, c_66, c_64, c_72, c_131, c_5929, c_6468])).
% 11.43/4.17  tff(c_6474, plain, (![B_584]: (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_3', B_584))=k2_pre_topc('#skF_4', k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', B_584)) | ~m1_subset_1(B_584, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_6472])).
% 11.43/4.17  tff(c_76, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_3', '#skF_6'))!=k2_pre_topc('#skF_4', k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6')) | ~v2_funct_1('#skF_5') | k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')!=k2_struct_0('#skF_4') | k1_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')!=k2_struct_0('#skF_3') | ~v3_tops_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_249])).
% 11.43/4.17  tff(c_5874, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_3', '#skF_6'))!=k2_pre_topc('#skF_4', k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5833, c_119, c_114, c_106, c_76])).
% 11.43/4.17  tff(c_6496, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6474, c_5874])).
% 11.43/4.17  tff(c_6523, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5831, c_6496])).
% 11.43/4.17  tff(c_6525, plain, (~v3_tops_2('#skF_5', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_80])).
% 11.43/4.17  tff(c_6527, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5832, c_6525])).
% 11.43/4.17  tff(c_6529, plain, (k1_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')!=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_98])).
% 11.43/4.17  tff(c_6528, plain, (v3_tops_2('#skF_5', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_98])).
% 11.43/4.17  tff(c_6591, plain, (![A_605, B_606, C_607]: (k1_relset_1(u1_struct_0(A_605), u1_struct_0(B_606), C_607)=k2_struct_0(A_605) | ~v3_tops_2(C_607, A_605, B_606) | ~m1_subset_1(C_607, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_605), u1_struct_0(B_606)))) | ~v1_funct_2(C_607, u1_struct_0(A_605), u1_struct_0(B_606)) | ~v1_funct_1(C_607) | ~l1_pre_topc(B_606) | ~l1_pre_topc(A_605))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.43/4.17  tff(c_6598, plain, (k1_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_3') | ~v3_tops_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_58, c_6591])).
% 11.43/4.17  tff(c_6602, plain, (k1_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_64, c_62, c_60, c_6528, c_6598])).
% 11.43/4.17  tff(c_6604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6529, c_6602])).
% 11.43/4.17  tff(c_6606, plain, (k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')!=k2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_92])).
% 11.43/4.17  tff(c_6605, plain, (v3_tops_2('#skF_5', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_92])).
% 11.43/4.17  tff(c_6675, plain, (![A_628, B_629, C_630]: (k2_relset_1(u1_struct_0(A_628), u1_struct_0(B_629), C_630)=k2_struct_0(B_629) | ~v3_tops_2(C_630, A_628, B_629) | ~m1_subset_1(C_630, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_628), u1_struct_0(B_629)))) | ~v1_funct_2(C_630, u1_struct_0(A_628), u1_struct_0(B_629)) | ~v1_funct_1(C_630) | ~l1_pre_topc(B_629) | ~l1_pre_topc(A_628))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.43/4.17  tff(c_6682, plain, (k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_4') | ~v3_tops_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_58, c_6675])).
% 11.43/4.17  tff(c_6686, plain, (k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_64, c_62, c_60, c_6605, c_6682])).
% 11.43/4.17  tff(c_6688, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6606, c_6686])).
% 11.43/4.17  tff(c_6690, plain, (~v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_86])).
% 11.43/4.17  tff(c_6689, plain, (v3_tops_2('#skF_5', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_86])).
% 11.43/4.17  tff(c_6722, plain, (![C_644, A_645, B_646]: (v2_funct_1(C_644) | ~v3_tops_2(C_644, A_645, B_646) | ~m1_subset_1(C_644, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_645), u1_struct_0(B_646)))) | ~v1_funct_2(C_644, u1_struct_0(A_645), u1_struct_0(B_646)) | ~v1_funct_1(C_644) | ~l1_pre_topc(B_646) | ~l1_pre_topc(A_645))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.43/4.17  tff(c_6729, plain, (v2_funct_1('#skF_5') | ~v3_tops_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_58, c_6722])).
% 11.43/4.17  tff(c_6733, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_64, c_62, c_60, c_6689, c_6729])).
% 11.43/4.17  tff(c_6735, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6690, c_6733])).
% 11.43/4.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.43/4.17  
% 11.43/4.17  Inference rules
% 11.43/4.17  ----------------------
% 11.43/4.17  #Ref     : 0
% 11.43/4.17  #Sup     : 1768
% 11.43/4.17  #Fact    : 0
% 11.43/4.17  #Define  : 0
% 11.43/4.17  #Split   : 18
% 11.43/4.17  #Chain   : 0
% 11.43/4.17  #Close   : 0
% 11.43/4.17  
% 11.43/4.17  Ordering : KBO
% 11.43/4.17  
% 11.43/4.17  Simplification rules
% 11.43/4.17  ----------------------
% 11.43/4.17  #Subsume      : 402
% 11.43/4.17  #Demod        : 1234
% 11.43/4.17  #Tautology    : 302
% 11.43/4.17  #SimpNegUnit  : 58
% 11.43/4.17  #BackRed      : 0
% 11.43/4.17  
% 11.43/4.17  #Partial instantiations: 0
% 11.43/4.17  #Strategies tried      : 1
% 11.43/4.17  
% 11.43/4.17  Timing (in seconds)
% 11.43/4.17  ----------------------
% 11.43/4.17  Preprocessing        : 0.42
% 11.43/4.17  Parsing              : 0.21
% 11.43/4.17  CNF conversion       : 0.04
% 11.43/4.17  Main loop            : 2.93
% 11.43/4.17  Inferencing          : 0.90
% 11.43/4.17  Reduction            : 1.02
% 11.43/4.17  Demodulation         : 0.75
% 11.43/4.17  BG Simplification    : 0.16
% 11.43/4.17  Subsumption          : 0.74
% 11.43/4.17  Abstraction          : 0.18
% 11.43/4.17  MUC search           : 0.00
% 11.43/4.17  Cooper               : 0.00
% 11.43/4.17  Total                : 3.42
% 11.43/4.17  Index Insertion      : 0.00
% 11.43/4.17  Index Deletion       : 0.00
% 11.43/4.17  Index Matching       : 0.00
% 11.43/4.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
