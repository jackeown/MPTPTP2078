%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1241+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:38 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 242 expanded)
%              Number of leaves         :   24 (  91 expanded)
%              Depth                    :   12
%              Number of atoms          :  153 ( 799 expanded)
%              Number of equality atoms :   36 ( 184 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( v3_pre_topc(D,B)
                       => k1_tops_1(B,D) = D )
                      & ( k1_tops_1(A,C) = C
                       => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_30,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_35,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_89,plain,(
    ! [A_33,B_34] :
      ( v3_pre_topc(k1_tops_1(A_33,B_34),A_33)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_96,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_89])).

tff(c_103,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_36,c_96])).

tff(c_105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_103])).

tff(c_107,plain,(
    k1_tops_1('#skF_1','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_32,plain,
    ( k1_tops_1('#skF_2','#skF_4') != '#skF_4'
    | k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_108,plain,(
    k1_tops_1('#skF_2','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_32])).

tff(c_22,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_109,plain,(
    ! [A_35,B_36] :
      ( k3_subset_1(A_35,k3_subset_1(A_35,B_36)) = B_36
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_114,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_109])).

tff(c_106,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_12,plain,(
    ! [A_10,B_12] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_10),B_12),A_10)
      | ~ v3_pre_topc(B_12,A_10)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k3_subset_1(A_4,B_5),k1_zfmisc_1(A_4))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_152,plain,(
    ! [A_41,B_42] :
      ( k2_pre_topc(A_41,B_42) = B_42
      | ~ v4_pre_topc(B_42,A_41)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_159,plain,
    ( k2_pre_topc('#skF_2','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_152])).

tff(c_166,plain,
    ( k2_pre_topc('#skF_2','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_159])).

tff(c_170,plain,(
    ~ v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_171,plain,(
    ! [A_43,B_44] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_43),B_44),A_43)
      | ~ v3_pre_topc(B_44,A_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_177,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_171])).

tff(c_181,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_177])).

tff(c_183,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_181])).

tff(c_184,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_187,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_4,c_184])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_187])).

tff(c_193,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_16,plain,(
    ! [A_13,B_15] :
      ( k2_pre_topc(A_13,B_15) = B_15
      | ~ v4_pre_topc(B_15,A_13)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_196,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_193,c_16])).

tff(c_203,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_196])).

tff(c_308,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_311,plain,
    ( ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_308])).

tff(c_315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_106,c_311])).

tff(c_316,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k3_subset_1(u1_struct_0(A_1),k2_pre_topc(A_1,k3_subset_1(u1_struct_0(A_1),B_3))) = k1_tops_1(A_1,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_406,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_2])).

tff(c_410,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_114,c_406])).

tff(c_412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_410])).

tff(c_414,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_28,plain,
    ( k1_tops_1('#skF_2','#skF_4') != '#skF_4'
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_415,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_415])).

tff(c_418,plain,(
    k1_tops_1('#skF_2','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_422,plain,(
    ! [A_53,B_54] :
      ( k3_subset_1(A_53,k3_subset_1(A_53,B_54)) = B_54
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_427,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_422])).

tff(c_413,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_589,plain,(
    ! [A_69,B_70] :
      ( k3_subset_1(u1_struct_0(A_69),k2_pre_topc(A_69,k3_subset_1(u1_struct_0(A_69),B_70))) = k1_tops_1(A_69,B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_623,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_4')) = k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_427,c_589])).

tff(c_629,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_4')) = k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_623])).

tff(c_640,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_629])).

tff(c_664,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_4,c_640])).

tff(c_668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_664])).

tff(c_670,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_629])).

tff(c_697,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_670,c_16])).

tff(c_707,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_697])).

tff(c_764,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_707])).

tff(c_800,plain,
    ( ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_764])).

tff(c_804,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_413,c_800])).

tff(c_805,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_707])).

tff(c_816,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_805,c_2])).

tff(c_820,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_427,c_816])).

tff(c_822,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_418,c_820])).

%------------------------------------------------------------------------------
