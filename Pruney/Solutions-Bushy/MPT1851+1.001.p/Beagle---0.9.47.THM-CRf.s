%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1851+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:32 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 102 expanded)
%              Number of leaves         :   18 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :   67 ( 231 expanded)
%              Number of equality atoms :   30 (  95 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v2_tdlat_3 > l1_pre_topc > k2_tarski > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_55,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v2_tdlat_3(A) )
             => v2_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tex_2)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
      <=> u1_pre_topc(A) = k2_tarski(k1_xboole_0,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tdlat_3)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    v2_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_1] :
      ( k2_tarski(k1_xboole_0,u1_struct_0(A_1)) = u1_pre_topc(A_1)
      | ~ v2_tdlat_3(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_12,plain,(
    ~ v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_2] :
      ( m1_subset_1(u1_pre_topc(A_2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_2))))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,(
    ! [C_13,A_14,D_15,B_16] :
      ( C_13 = A_14
      | g1_pre_topc(C_13,D_15) != g1_pre_topc(A_14,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(k1_zfmisc_1(A_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_49,plain,(
    ! [A_17,B_18] :
      ( u1_struct_0('#skF_2') = A_17
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_17,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_44])).

tff(c_53,plain,(
    ! [A_2] :
      ( u1_struct_0(A_2) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_2),u1_pre_topc(A_2)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(A_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_70,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_53])).

tff(c_72,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_70])).

tff(c_2,plain,(
    ! [A_1] :
      ( v2_tdlat_3(A_1)
      | k2_tarski(k1_xboole_0,u1_struct_0(A_1)) != u1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_90,plain,
    ( v2_tdlat_3('#skF_2')
    | k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_2])).

tff(c_99,plain,
    ( v2_tdlat_3('#skF_2')
    | k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_90])).

tff(c_100,plain,(
    k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_99])).

tff(c_106,plain,
    ( u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1')
    | ~ v2_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_100])).

tff(c_108,plain,(
    u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14,c_106])).

tff(c_58,plain,(
    ! [D_19,B_20,C_21,A_22] :
      ( D_19 = B_20
      | g1_pre_topc(C_21,D_19) != g1_pre_topc(A_22,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(A_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_62,plain,(
    ! [D_19,C_21] :
      ( u1_pre_topc('#skF_2') = D_19
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_21,D_19)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_58])).

tff(c_109,plain,(
    ! [D_19,C_21] :
      ( u1_pre_topc('#skF_2') = D_19
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_21,D_19)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_62])).

tff(c_110,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_93,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_6])).

tff(c_102,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_93])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_102])).

tff(c_112,plain,(
    ! [D_19,C_21] :
      ( u1_pre_topc('#skF_2') = D_19
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_21,D_19) ) ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_136,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_112])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_136])).

%------------------------------------------------------------------------------
