%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:48 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 272 expanded)
%              Number of leaves         :   24 ( 100 expanded)
%              Depth                    :   12
%              Number of atoms          :  168 ( 928 expanded)
%              Number of equality atoms :   36 ( 199 expanded)
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

tff(f_94,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_30,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_35,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_61,plain,(
    ! [A_31,B_32] :
      ( v3_pre_topc(k1_tops_1(A_31,B_32),A_31)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_68,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_61])).

tff(c_75,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_36,c_68])).

tff(c_77,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_75])).

tff(c_79,plain,(
    k1_tops_1('#skF_1','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_32,plain,
    ( k1_tops_1('#skF_2','#skF_4') != '#skF_4'
    | k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_80,plain,(
    k1_tops_1('#skF_2','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_32])).

tff(c_22,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_82,plain,(
    ! [A_35,B_36] :
      ( k3_subset_1(A_35,k3_subset_1(A_35,B_36)) = B_36
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_90,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_82])).

tff(c_78,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_16,plain,(
    ! [A_13,B_15] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_13),B_15),A_13)
      | ~ v3_pre_topc(B_15,A_13)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_123,plain,(
    ! [A_39,B_40] :
      ( k2_pre_topc(A_39,B_40) = B_40
      | ~ v4_pre_topc(B_40,A_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_130,plain,
    ( k2_pre_topc('#skF_2','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_123])).

tff(c_137,plain,
    ( k2_pre_topc('#skF_2','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_130])).

tff(c_142,plain,(
    ~ v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_227,plain,(
    ! [A_47,B_48] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_47),B_48),A_47)
      | ~ v3_pre_topc(B_48,A_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_240,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_227])).

tff(c_246,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_240])).

tff(c_247,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_246])).

tff(c_258,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_282,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_2,c_258])).

tff(c_286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_282])).

tff(c_288,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_8,plain,(
    ! [A_5,B_7] :
      ( k2_pre_topc(A_5,B_7) = B_7
      | ~ v4_pre_topc(B_7,A_5)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_356,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_288,c_8])).

tff(c_366,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_356])).

tff(c_408,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_366])).

tff(c_411,plain,
    ( ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_408])).

tff(c_415,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_78,c_411])).

tff(c_416,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_366])).

tff(c_10,plain,(
    ! [A_8,B_10] :
      ( k3_subset_1(u1_struct_0(A_8),k2_pre_topc(A_8,k3_subset_1(u1_struct_0(A_8),B_10))) = k1_tops_1(A_8,B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_450,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_10])).

tff(c_454,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_90,c_450])).

tff(c_456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_454])).

tff(c_458,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_28,plain,
    ( k1_tops_1('#skF_2','#skF_4') != '#skF_4'
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_459,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_459])).

tff(c_462,plain,(
    k1_tops_1('#skF_2','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_467,plain,(
    ! [A_55,B_56] :
      ( k3_subset_1(A_55,k3_subset_1(A_55,B_56)) = B_56
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_475,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_467])).

tff(c_457,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_493,plain,(
    ! [A_57,B_58] :
      ( k2_pre_topc(A_57,B_58) = B_58
      | ~ v4_pre_topc(B_58,A_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_500,plain,
    ( k2_pre_topc('#skF_2','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_493])).

tff(c_507,plain,
    ( k2_pre_topc('#skF_2','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_500])).

tff(c_511,plain,(
    ~ v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_507])).

tff(c_597,plain,(
    ! [A_65,B_66] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_65),B_66),A_65)
      | ~ v3_pre_topc(B_66,A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_607,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_597])).

tff(c_612,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_607])).

tff(c_613,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_511,c_612])).

tff(c_664,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_613])).

tff(c_667,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_2,c_664])).

tff(c_671,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_667])).

tff(c_673,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_613])).

tff(c_681,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_673,c_8])).

tff(c_692,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_681])).

tff(c_841,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_692])).

tff(c_872,plain,
    ( ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_841])).

tff(c_876,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_457,c_872])).

tff(c_877,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_692])).

tff(c_888,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_877,c_10])).

tff(c_892,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_475,c_888])).

tff(c_894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_462,c_892])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.48  
% 3.03/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.49  %$ v4_pre_topc > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.03/1.49  
% 3.03/1.49  %Foreground sorts:
% 3.03/1.49  
% 3.03/1.49  
% 3.03/1.49  %Background operators:
% 3.03/1.49  
% 3.03/1.49  
% 3.03/1.49  %Foreground operators:
% 3.03/1.49  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.03/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.03/1.49  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.03/1.49  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.03/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.03/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.03/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.03/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.03/1.49  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.03/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.03/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.03/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.03/1.49  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.03/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.03/1.49  
% 3.03/1.50  tff(f_94, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 3.03/1.50  tff(f_63, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.03/1.50  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.03/1.50  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 3.03/1.50  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.03/1.50  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.03/1.50  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 3.03/1.50  tff(c_30, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.03/1.50  tff(c_35, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_30])).
% 3.03/1.50  tff(c_26, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.03/1.50  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.03/1.50  tff(c_34, plain, (v3_pre_topc('#skF_4', '#skF_2') | k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.03/1.50  tff(c_36, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_34])).
% 3.03/1.50  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.03/1.50  tff(c_61, plain, (![A_31, B_32]: (v3_pre_topc(k1_tops_1(A_31, B_32), A_31) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.03/1.50  tff(c_68, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_61])).
% 3.03/1.50  tff(c_75, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_36, c_68])).
% 3.03/1.50  tff(c_77, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_75])).
% 3.03/1.50  tff(c_79, plain, (k1_tops_1('#skF_1', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 3.03/1.50  tff(c_32, plain, (k1_tops_1('#skF_2', '#skF_4')!='#skF_4' | k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.03/1.50  tff(c_80, plain, (k1_tops_1('#skF_2', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_79, c_32])).
% 3.03/1.50  tff(c_22, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.03/1.50  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.03/1.50  tff(c_82, plain, (![A_35, B_36]: (k3_subset_1(A_35, k3_subset_1(A_35, B_36))=B_36 | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.03/1.50  tff(c_90, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_18, c_82])).
% 3.03/1.50  tff(c_78, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_34])).
% 3.03/1.50  tff(c_16, plain, (![A_13, B_15]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_13), B_15), A_13) | ~v3_pre_topc(B_15, A_13) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.03/1.50  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.03/1.50  tff(c_123, plain, (![A_39, B_40]: (k2_pre_topc(A_39, B_40)=B_40 | ~v4_pre_topc(B_40, A_39) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.03/1.50  tff(c_130, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_123])).
% 3.03/1.50  tff(c_137, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_130])).
% 3.03/1.50  tff(c_142, plain, (~v4_pre_topc('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_137])).
% 3.03/1.50  tff(c_227, plain, (![A_47, B_48]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_47), B_48), A_47) | ~v3_pre_topc(B_48, A_47) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.03/1.50  tff(c_240, plain, (v4_pre_topc('#skF_4', '#skF_2') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_227])).
% 3.03/1.50  tff(c_246, plain, (v4_pre_topc('#skF_4', '#skF_2') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_240])).
% 3.03/1.50  tff(c_247, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_142, c_246])).
% 3.03/1.50  tff(c_258, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_247])).
% 3.03/1.50  tff(c_282, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_2, c_258])).
% 3.03/1.50  tff(c_286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_282])).
% 3.03/1.50  tff(c_288, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_247])).
% 3.03/1.50  tff(c_8, plain, (![A_5, B_7]: (k2_pre_topc(A_5, B_7)=B_7 | ~v4_pre_topc(B_7, A_5) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.03/1.50  tff(c_356, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_288, c_8])).
% 3.03/1.50  tff(c_366, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_356])).
% 3.03/1.50  tff(c_408, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_366])).
% 3.03/1.50  tff(c_411, plain, (~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_408])).
% 3.03/1.50  tff(c_415, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_78, c_411])).
% 3.03/1.50  tff(c_416, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), inference(splitRight, [status(thm)], [c_366])).
% 3.03/1.50  tff(c_10, plain, (![A_8, B_10]: (k3_subset_1(u1_struct_0(A_8), k2_pre_topc(A_8, k3_subset_1(u1_struct_0(A_8), B_10)))=k1_tops_1(A_8, B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.03/1.50  tff(c_450, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_416, c_10])).
% 3.03/1.50  tff(c_454, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_90, c_450])).
% 3.03/1.50  tff(c_456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_454])).
% 3.03/1.50  tff(c_458, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 3.03/1.50  tff(c_28, plain, (k1_tops_1('#skF_2', '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.03/1.50  tff(c_459, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 3.03/1.50  tff(c_461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_458, c_459])).
% 3.03/1.50  tff(c_462, plain, (k1_tops_1('#skF_2', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_28])).
% 3.03/1.50  tff(c_467, plain, (![A_55, B_56]: (k3_subset_1(A_55, k3_subset_1(A_55, B_56))=B_56 | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.03/1.50  tff(c_475, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_18, c_467])).
% 3.03/1.50  tff(c_457, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_30])).
% 3.03/1.50  tff(c_493, plain, (![A_57, B_58]: (k2_pre_topc(A_57, B_58)=B_58 | ~v4_pre_topc(B_58, A_57) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.03/1.50  tff(c_500, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_493])).
% 3.03/1.50  tff(c_507, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_500])).
% 3.03/1.50  tff(c_511, plain, (~v4_pre_topc('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_507])).
% 3.03/1.50  tff(c_597, plain, (![A_65, B_66]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_65), B_66), A_65) | ~v3_pre_topc(B_66, A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.03/1.50  tff(c_607, plain, (v4_pre_topc('#skF_4', '#skF_2') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_475, c_597])).
% 3.03/1.50  tff(c_612, plain, (v4_pre_topc('#skF_4', '#skF_2') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_607])).
% 3.03/1.50  tff(c_613, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_511, c_612])).
% 3.03/1.50  tff(c_664, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_613])).
% 3.03/1.50  tff(c_667, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_2, c_664])).
% 3.03/1.50  tff(c_671, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_667])).
% 3.03/1.50  tff(c_673, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_613])).
% 3.03/1.50  tff(c_681, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_673, c_8])).
% 3.03/1.50  tff(c_692, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_681])).
% 3.03/1.50  tff(c_841, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_692])).
% 3.03/1.50  tff(c_872, plain, (~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_841])).
% 3.03/1.50  tff(c_876, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_457, c_872])).
% 3.03/1.50  tff(c_877, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), inference(splitRight, [status(thm)], [c_692])).
% 3.03/1.50  tff(c_888, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_877, c_10])).
% 3.03/1.50  tff(c_892, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_475, c_888])).
% 3.03/1.50  tff(c_894, plain, $false, inference(negUnitSimplification, [status(thm)], [c_462, c_892])).
% 3.03/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.50  
% 3.03/1.50  Inference rules
% 3.03/1.50  ----------------------
% 3.03/1.50  #Ref     : 0
% 3.03/1.50  #Sup     : 183
% 3.03/1.50  #Fact    : 0
% 3.03/1.50  #Define  : 0
% 3.03/1.50  #Split   : 19
% 3.03/1.50  #Chain   : 0
% 3.03/1.50  #Close   : 0
% 3.03/1.51  
% 3.03/1.51  Ordering : KBO
% 3.03/1.51  
% 3.03/1.51  Simplification rules
% 3.03/1.51  ----------------------
% 3.03/1.51  #Subsume      : 23
% 3.03/1.51  #Demod        : 149
% 3.03/1.51  #Tautology    : 69
% 3.03/1.51  #SimpNegUnit  : 15
% 3.03/1.51  #BackRed      : 1
% 3.03/1.51  
% 3.03/1.51  #Partial instantiations: 0
% 3.03/1.51  #Strategies tried      : 1
% 3.03/1.51  
% 3.03/1.51  Timing (in seconds)
% 3.03/1.51  ----------------------
% 3.16/1.51  Preprocessing        : 0.33
% 3.16/1.51  Parsing              : 0.18
% 3.16/1.51  CNF conversion       : 0.03
% 3.16/1.51  Main loop            : 0.38
% 3.16/1.51  Inferencing          : 0.14
% 3.16/1.51  Reduction            : 0.12
% 3.16/1.51  Demodulation         : 0.09
% 3.16/1.51  BG Simplification    : 0.02
% 3.16/1.51  Subsumption          : 0.07
% 3.16/1.51  Abstraction          : 0.02
% 3.16/1.51  MUC search           : 0.00
% 3.16/1.51  Cooper               : 0.00
% 3.16/1.51  Total                : 0.75
% 3.16/1.51  Index Insertion      : 0.00
% 3.16/1.51  Index Deletion       : 0.00
% 3.16/1.51  Index Matching       : 0.00
% 3.16/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
