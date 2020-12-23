%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:25 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 428 expanded)
%              Number of leaves         :   40 ( 159 expanded)
%              Depth                    :   12
%              Number of atoms          :  213 (1207 expanded)
%              Number of equality atoms :   15 ( 181 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_31,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_29,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_pre_topc)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_38,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_26,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_99,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_104,plain,(
    ! [A_47] :
      ( u1_struct_0(A_47) = k2_struct_0(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_26,c_99])).

tff(c_108,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_104])).

tff(c_28,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_114,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_28])).

tff(c_117,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_114])).

tff(c_119,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_134,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_119])).

tff(c_138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_134])).

tff(c_139,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_110,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_42])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_32,plain,(
    ! [A_21] :
      ( v3_pre_topc(k2_struct_0(A_21),A_21)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_260,plain,(
    ! [B_74,A_75] :
      ( v3_pre_topc(B_74,A_75)
      | ~ r2_hidden(B_74,u1_pre_topc(A_75))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_290,plain,(
    ! [A_78] :
      ( v3_pre_topc(u1_struct_0(A_78),A_78)
      | ~ r2_hidden(u1_struct_0(A_78),u1_pre_topc(A_78))
      | ~ l1_pre_topc(A_78) ) ),
    inference(resolution,[status(thm)],[c_60,c_260])).

tff(c_296,plain,
    ( v3_pre_topc(u1_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_290])).

tff(c_299,plain,
    ( v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_108,c_296])).

tff(c_316,plain,(
    ~ r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_233,plain,(
    ! [B_69,A_70] :
      ( r2_hidden(B_69,u1_pre_topc(A_70))
      | ~ v3_pre_topc(B_69,A_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_361,plain,(
    ! [A_83] :
      ( r2_hidden(u1_struct_0(A_83),u1_pre_topc(A_83))
      | ~ v3_pre_topc(u1_struct_0(A_83),A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_60,c_233])).

tff(c_373,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc(u1_struct_0('#skF_1'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_361])).

tff(c_378,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_108,c_373])).

tff(c_379,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_378])).

tff(c_382,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_379])).

tff(c_386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_382])).

tff(c_387,plain,(
    v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_12])).

tff(c_4,plain,(
    ! [A_2] : k1_subset_1(A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    ! [A_2] : k1_subset_1(A_2) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4])).

tff(c_10,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_subset_1(A_5)) = k2_subset_1(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_61,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_subset_1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_63,plain,(
    ! [A_5] : k3_subset_1(A_5,'#skF_3') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_61])).

tff(c_397,plain,(
    ! [B_84,A_85] :
      ( v3_pre_topc(B_84,A_85)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(A_85),B_84),A_85)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_404,plain,(
    ! [A_85] :
      ( v3_pre_topc('#skF_3',A_85)
      | ~ v4_pre_topc(u1_struct_0(A_85),A_85)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_397])).

tff(c_409,plain,(
    ! [A_86] :
      ( v3_pre_topc('#skF_3',A_86)
      | ~ v4_pre_topc(u1_struct_0(A_86),A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_404])).

tff(c_412,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_409])).

tff(c_414,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_412])).

tff(c_415,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_414])).

tff(c_30,plain,(
    ! [A_20] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_20))
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_57,plain,(
    ! [A_20] :
      ( r2_hidden('#skF_3',u1_pre_topc(A_20))
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30])).

tff(c_276,plain,(
    ! [A_76] :
      ( v3_pre_topc('#skF_3',A_76)
      | ~ r2_hidden('#skF_3',u1_pre_topc(A_76))
      | ~ l1_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_58,c_260])).

tff(c_287,plain,(
    ! [A_20] :
      ( v3_pre_topc('#skF_3',A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(resolution,[status(thm)],[c_57,c_276])).

tff(c_54,plain,(
    ! [D_36] :
      ( v4_pre_topc(D_36,'#skF_1')
      | ~ r2_hidden(D_36,'#skF_3')
      | ~ m1_subset_1(D_36,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_165,plain,(
    ! [D_57] :
      ( v4_pre_topc(D_57,'#skF_1')
      | ~ r2_hidden(D_57,'#skF_3')
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_54])).

tff(c_174,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ r2_hidden('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_165])).

tff(c_177,plain,(
    ~ r2_hidden('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_50,plain,(
    ! [D_36] :
      ( r2_hidden(D_36,'#skF_3')
      | ~ r2_hidden('#skF_2',D_36)
      | ~ v4_pre_topc(D_36,'#skF_1')
      | ~ v3_pre_topc(D_36,'#skF_1')
      | ~ m1_subset_1(D_36,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_301,plain,(
    ! [D_79] :
      ( r2_hidden(D_79,'#skF_3')
      | ~ r2_hidden('#skF_2',D_79)
      | ~ v4_pre_topc(D_79,'#skF_1')
      | ~ v3_pre_topc(D_79,'#skF_1')
      | ~ m1_subset_1(D_79,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_50])).

tff(c_305,plain,
    ( r2_hidden('#skF_3','#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_301])).

tff(c_312,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_305])).

tff(c_416,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_419,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_287,c_416])).

tff(c_423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_419])).

tff(c_425,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_427,plain,(
    ! [A_87,B_88] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_87),B_88),A_87)
      | ~ v3_pre_topc(B_88,A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_437,plain,(
    ! [A_87] :
      ( v4_pre_topc(u1_struct_0(A_87),A_87)
      | ~ v3_pre_topc('#skF_3',A_87)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_427])).

tff(c_447,plain,(
    ! [A_89] :
      ( v4_pre_topc(u1_struct_0(A_89),A_89)
      | ~ v3_pre_topc('#skF_3',A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_437])).

tff(c_453,plain,
    ( v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_447])).

tff(c_456,plain,(
    v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_425,c_453])).

tff(c_458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_415,c_456])).

tff(c_460,plain,(
    v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_414])).

tff(c_175,plain,
    ( v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_165])).

tff(c_182,plain,(
    ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_309,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),'#skF_3')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_301])).

tff(c_315,plain,
    ( ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_309])).

tff(c_579,plain,(
    ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_460,c_315])).

tff(c_582,plain,
    ( v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_14,c_579])).

tff(c_585,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_582])).

tff(c_587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_585])).

tff(c_589,plain,(
    r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( ~ r1_tarski(B_13,A_12)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_599,plain,(
    ~ r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_589,c_18])).

tff(c_603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_599])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:46:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.38  
% 2.74/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.38  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.74/1.38  
% 2.74/1.38  %Foreground sorts:
% 2.74/1.38  
% 2.74/1.38  
% 2.74/1.38  %Background operators:
% 2.74/1.38  
% 2.74/1.38  
% 2.74/1.38  %Foreground operators:
% 2.74/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.74/1.38  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.74/1.38  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.74/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.74/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.38  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.74/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.74/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.38  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.74/1.38  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.74/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.38  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.74/1.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.74/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.74/1.38  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.74/1.38  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.74/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.74/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.38  
% 2.74/1.41  tff(f_128, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.74/1.41  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.74/1.41  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.74/1.41  tff(f_58, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.74/1.41  tff(f_79, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.74/1.41  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.74/1.41  tff(f_91, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.74/1.41  tff(f_31, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.74/1.41  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.74/1.41  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.74/1.41  tff(f_37, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.74/1.41  tff(f_29, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.74/1.41  tff(f_35, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 2.74/1.41  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 2.74/1.41  tff(f_85, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => r2_hidden(k1_xboole_0, u1_pre_topc(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_pre_topc)).
% 2.74/1.41  tff(f_54, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.74/1.41  tff(c_38, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.74/1.41  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.74/1.41  tff(c_64, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2])).
% 2.74/1.41  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.74/1.41  tff(c_26, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.74/1.41  tff(c_48, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.74/1.41  tff(c_99, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.74/1.41  tff(c_104, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_26, c_99])).
% 2.74/1.41  tff(c_108, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_104])).
% 2.74/1.41  tff(c_28, plain, (![A_19]: (~v1_xboole_0(u1_struct_0(A_19)) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.74/1.41  tff(c_114, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_108, c_28])).
% 2.74/1.41  tff(c_117, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_48, c_114])).
% 2.74/1.41  tff(c_119, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_117])).
% 2.74/1.41  tff(c_134, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_119])).
% 2.74/1.41  tff(c_138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_134])).
% 2.74/1.41  tff(c_139, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_117])).
% 2.74/1.41  tff(c_42, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.74/1.41  tff(c_110, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_42])).
% 2.74/1.41  tff(c_14, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.74/1.41  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.74/1.41  tff(c_32, plain, (![A_21]: (v3_pre_topc(k2_struct_0(A_21), A_21) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.74/1.41  tff(c_6, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.41  tff(c_8, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.74/1.41  tff(c_60, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.74/1.41  tff(c_260, plain, (![B_74, A_75]: (v3_pre_topc(B_74, A_75) | ~r2_hidden(B_74, u1_pre_topc(A_75)) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.74/1.41  tff(c_290, plain, (![A_78]: (v3_pre_topc(u1_struct_0(A_78), A_78) | ~r2_hidden(u1_struct_0(A_78), u1_pre_topc(A_78)) | ~l1_pre_topc(A_78))), inference(resolution, [status(thm)], [c_60, c_260])).
% 2.74/1.41  tff(c_296, plain, (v3_pre_topc(u1_struct_0('#skF_1'), '#skF_1') | ~r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_108, c_290])).
% 2.74/1.41  tff(c_299, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_108, c_296])).
% 2.74/1.41  tff(c_316, plain, (~r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(splitLeft, [status(thm)], [c_299])).
% 2.74/1.41  tff(c_233, plain, (![B_69, A_70]: (r2_hidden(B_69, u1_pre_topc(A_70)) | ~v3_pre_topc(B_69, A_70) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.74/1.41  tff(c_361, plain, (![A_83]: (r2_hidden(u1_struct_0(A_83), u1_pre_topc(A_83)) | ~v3_pre_topc(u1_struct_0(A_83), A_83) | ~l1_pre_topc(A_83))), inference(resolution, [status(thm)], [c_60, c_233])).
% 2.74/1.41  tff(c_373, plain, (r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v3_pre_topc(u1_struct_0('#skF_1'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_108, c_361])).
% 2.74/1.41  tff(c_378, plain, (r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_108, c_373])).
% 2.74/1.41  tff(c_379, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_316, c_378])).
% 2.74/1.41  tff(c_382, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_379])).
% 2.74/1.41  tff(c_386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_382])).
% 2.74/1.41  tff(c_387, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_299])).
% 2.74/1.41  tff(c_12, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.74/1.41  tff(c_58, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_12])).
% 2.74/1.41  tff(c_4, plain, (![A_2]: (k1_subset_1(A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.74/1.41  tff(c_62, plain, (![A_2]: (k1_subset_1(A_2)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4])).
% 2.74/1.41  tff(c_10, plain, (![A_5]: (k3_subset_1(A_5, k1_subset_1(A_5))=k2_subset_1(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.74/1.41  tff(c_61, plain, (![A_5]: (k3_subset_1(A_5, k1_subset_1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 2.74/1.41  tff(c_63, plain, (![A_5]: (k3_subset_1(A_5, '#skF_3')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_61])).
% 2.74/1.41  tff(c_397, plain, (![B_84, A_85]: (v3_pre_topc(B_84, A_85) | ~v4_pre_topc(k3_subset_1(u1_struct_0(A_85), B_84), A_85) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.74/1.41  tff(c_404, plain, (![A_85]: (v3_pre_topc('#skF_3', A_85) | ~v4_pre_topc(u1_struct_0(A_85), A_85) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(superposition, [status(thm), theory('equality')], [c_63, c_397])).
% 2.74/1.41  tff(c_409, plain, (![A_86]: (v3_pre_topc('#skF_3', A_86) | ~v4_pre_topc(u1_struct_0(A_86), A_86) | ~l1_pre_topc(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_404])).
% 2.74/1.41  tff(c_412, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_108, c_409])).
% 2.74/1.41  tff(c_414, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_412])).
% 2.74/1.41  tff(c_415, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_414])).
% 2.74/1.41  tff(c_30, plain, (![A_20]: (r2_hidden(k1_xboole_0, u1_pre_topc(A_20)) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.74/1.41  tff(c_57, plain, (![A_20]: (r2_hidden('#skF_3', u1_pre_topc(A_20)) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30])).
% 2.74/1.41  tff(c_276, plain, (![A_76]: (v3_pre_topc('#skF_3', A_76) | ~r2_hidden('#skF_3', u1_pre_topc(A_76)) | ~l1_pre_topc(A_76))), inference(resolution, [status(thm)], [c_58, c_260])).
% 2.74/1.41  tff(c_287, plain, (![A_20]: (v3_pre_topc('#skF_3', A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(resolution, [status(thm)], [c_57, c_276])).
% 2.74/1.41  tff(c_54, plain, (![D_36]: (v4_pre_topc(D_36, '#skF_1') | ~r2_hidden(D_36, '#skF_3') | ~m1_subset_1(D_36, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.74/1.41  tff(c_165, plain, (![D_57]: (v4_pre_topc(D_57, '#skF_1') | ~r2_hidden(D_57, '#skF_3') | ~m1_subset_1(D_57, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_54])).
% 2.74/1.41  tff(c_174, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~r2_hidden('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_165])).
% 2.74/1.41  tff(c_177, plain, (~r2_hidden('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_174])).
% 2.74/1.41  tff(c_50, plain, (![D_36]: (r2_hidden(D_36, '#skF_3') | ~r2_hidden('#skF_2', D_36) | ~v4_pre_topc(D_36, '#skF_1') | ~v3_pre_topc(D_36, '#skF_1') | ~m1_subset_1(D_36, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.74/1.41  tff(c_301, plain, (![D_79]: (r2_hidden(D_79, '#skF_3') | ~r2_hidden('#skF_2', D_79) | ~v4_pre_topc(D_79, '#skF_1') | ~v3_pre_topc(D_79, '#skF_1') | ~m1_subset_1(D_79, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_50])).
% 2.74/1.41  tff(c_305, plain, (r2_hidden('#skF_3', '#skF_3') | ~r2_hidden('#skF_2', '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_301])).
% 2.74/1.41  tff(c_312, plain, (~r2_hidden('#skF_2', '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_177, c_305])).
% 2.74/1.41  tff(c_416, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_312])).
% 2.74/1.41  tff(c_419, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_287, c_416])).
% 2.74/1.41  tff(c_423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_419])).
% 2.74/1.41  tff(c_425, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_312])).
% 2.74/1.41  tff(c_427, plain, (![A_87, B_88]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_87), B_88), A_87) | ~v3_pre_topc(B_88, A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.74/1.41  tff(c_437, plain, (![A_87]: (v4_pre_topc(u1_struct_0(A_87), A_87) | ~v3_pre_topc('#skF_3', A_87) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(superposition, [status(thm), theory('equality')], [c_63, c_427])).
% 2.74/1.41  tff(c_447, plain, (![A_89]: (v4_pre_topc(u1_struct_0(A_89), A_89) | ~v3_pre_topc('#skF_3', A_89) | ~l1_pre_topc(A_89))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_437])).
% 2.74/1.41  tff(c_453, plain, (v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_108, c_447])).
% 2.74/1.41  tff(c_456, plain, (v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_425, c_453])).
% 2.74/1.41  tff(c_458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_415, c_456])).
% 2.74/1.41  tff(c_460, plain, (v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_414])).
% 2.74/1.41  tff(c_175, plain, (v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_60, c_165])).
% 2.74/1.41  tff(c_182, plain, (~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_175])).
% 2.74/1.41  tff(c_309, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_60, c_301])).
% 2.74/1.41  tff(c_315, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_182, c_309])).
% 2.74/1.41  tff(c_579, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_387, c_460, c_315])).
% 2.74/1.41  tff(c_582, plain, (v1_xboole_0(k2_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_579])).
% 2.74/1.41  tff(c_585, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_582])).
% 2.74/1.41  tff(c_587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_585])).
% 2.74/1.41  tff(c_589, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_175])).
% 2.74/1.41  tff(c_18, plain, (![B_13, A_12]: (~r1_tarski(B_13, A_12) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.74/1.41  tff(c_599, plain, (~r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_589, c_18])).
% 2.74/1.41  tff(c_603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_599])).
% 2.74/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.41  
% 2.74/1.41  Inference rules
% 2.74/1.41  ----------------------
% 2.74/1.41  #Ref     : 0
% 2.74/1.41  #Sup     : 97
% 2.74/1.41  #Fact    : 0
% 2.74/1.41  #Define  : 0
% 2.74/1.41  #Split   : 12
% 2.74/1.41  #Chain   : 0
% 2.74/1.41  #Close   : 0
% 2.74/1.41  
% 2.74/1.41  Ordering : KBO
% 2.74/1.41  
% 2.74/1.41  Simplification rules
% 2.74/1.41  ----------------------
% 2.74/1.41  #Subsume      : 12
% 2.74/1.41  #Demod        : 73
% 2.74/1.41  #Tautology    : 30
% 2.74/1.41  #SimpNegUnit  : 6
% 2.74/1.41  #BackRed      : 1
% 2.74/1.41  
% 2.74/1.41  #Partial instantiations: 0
% 2.74/1.41  #Strategies tried      : 1
% 2.74/1.41  
% 2.74/1.41  Timing (in seconds)
% 2.74/1.41  ----------------------
% 2.74/1.41  Preprocessing        : 0.33
% 2.74/1.41  Parsing              : 0.17
% 2.74/1.41  CNF conversion       : 0.02
% 2.74/1.41  Main loop            : 0.32
% 2.74/1.41  Inferencing          : 0.12
% 2.74/1.41  Reduction            : 0.10
% 2.74/1.41  Demodulation         : 0.07
% 2.74/1.41  BG Simplification    : 0.02
% 2.74/1.41  Subsumption          : 0.05
% 2.74/1.41  Abstraction          : 0.01
% 2.74/1.41  MUC search           : 0.00
% 2.74/1.41  Cooper               : 0.00
% 2.74/1.41  Total                : 0.69
% 2.74/1.41  Index Insertion      : 0.00
% 2.74/1.41  Index Deletion       : 0.00
% 2.74/1.41  Index Matching       : 0.00
% 2.74/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
