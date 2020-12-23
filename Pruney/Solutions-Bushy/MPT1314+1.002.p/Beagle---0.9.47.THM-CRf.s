%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1314+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:47 EST 2020

% Result     : Theorem 8.31s
% Output     : CNFRefutation 8.31s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 233 expanded)
%              Number of leaves         :   29 (  92 expanded)
%              Depth                    :   12
%              Number of atoms          :  118 ( 544 expanded)
%              Number of equality atoms :   16 (  78 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( v3_pre_topc(B,A)
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                     => ( D = B
                       => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_28,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => ( v3_pre_topc(C,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v3_pre_topc(D,A)
                    & k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_2)).

tff(c_30,plain,(
    '#skF_5' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_28,plain,(
    ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_42,plain,(
    ~ v3_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_8,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_48,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k2_struct_0(A_51)
      | ~ l1_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_62,plain,(
    ! [A_54] :
      ( u1_struct_0(A_54) = k2_struct_0(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_8,c_48])).

tff(c_66,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_62])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_53,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_60,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_53])).

tff(c_67,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60])).

tff(c_34,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_100,plain,(
    ! [B_59,A_60] :
      ( l1_pre_topc(B_59)
      | ~ m1_pre_topc(B_59,A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_103,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_100])).

tff(c_106,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_103])).

tff(c_52,plain,(
    ! [A_6] :
      ( u1_struct_0(A_6) = k2_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_48])).

tff(c_110,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_52])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_41,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32])).

tff(c_61,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_41,c_53])).

tff(c_73,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(A_55,B_56) = A_55
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_81,plain,(
    k3_xboole_0('#skF_3',u1_struct_0('#skF_4')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_61,c_73])).

tff(c_111,plain,(
    k3_xboole_0('#skF_3',k2_struct_0('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_81])).

tff(c_126,plain,(
    ! [A_61] :
      ( m1_subset_1(k2_struct_0(A_61),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_143,plain,(
    ! [A_62] :
      ( r1_tarski(k2_struct_0(A_62),u1_struct_0(A_62))
      | ~ l1_struct_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_126,c_24])).

tff(c_149,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_143])).

tff(c_173,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_176,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_173])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_176])).

tff(c_182,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_132,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_126])).

tff(c_213,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_132])).

tff(c_243,plain,(
    ! [A_70,B_71,C_72] :
      ( k9_subset_1(A_70,B_71,C_72) = k3_xboole_0(B_71,C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_258,plain,(
    ! [B_71] : k9_subset_1(k2_struct_0('#skF_4'),B_71,k2_struct_0('#skF_4')) = k3_xboole_0(B_71,k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_213,c_243])).

tff(c_6,plain,(
    ! [A_3,B_4,C_5] :
      ( m1_subset_1(k9_subset_1(A_3,B_4,C_5),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_26,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(A_37,k1_zfmisc_1(B_38))
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_700,plain,(
    ! [B_110,D_111,A_112] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_110),D_111,k2_struct_0(B_110)),B_110)
      | ~ v3_pre_topc(D_111,A_112)
      | ~ m1_subset_1(D_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_110),D_111,k2_struct_0(B_110)),k1_zfmisc_1(u1_struct_0(B_110)))
      | ~ m1_pre_topc(B_110,A_112)
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2268,plain,(
    ! [B_260,A_261,A_262] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_260),A_261,k2_struct_0(B_260)),B_260)
      | ~ v3_pre_topc(A_261,A_262)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_260),A_261,k2_struct_0(B_260)),k1_zfmisc_1(u1_struct_0(B_260)))
      | ~ m1_pre_topc(B_260,A_262)
      | ~ l1_pre_topc(A_262)
      | ~ r1_tarski(A_261,u1_struct_0(A_262)) ) ),
    inference(resolution,[status(thm)],[c_26,c_700])).

tff(c_6014,plain,(
    ! [B_538,B_539,A_540] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_538),B_539,k2_struct_0(B_538)),B_538)
      | ~ v3_pre_topc(B_539,A_540)
      | ~ m1_pre_topc(B_538,A_540)
      | ~ l1_pre_topc(A_540)
      | ~ r1_tarski(B_539,u1_struct_0(A_540))
      | ~ m1_subset_1(k2_struct_0(B_538),k1_zfmisc_1(u1_struct_0(B_538))) ) ),
    inference(resolution,[status(thm)],[c_6,c_2268])).

tff(c_6016,plain,(
    ! [B_539] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0('#skF_4'),B_539,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v3_pre_topc(B_539,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(B_539,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_36,c_6014])).

tff(c_6020,plain,(
    ! [B_541] :
      ( v3_pre_topc(k3_xboole_0(B_541,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v3_pre_topc(B_541,'#skF_2')
      | ~ r1_tarski(B_541,k2_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_110,c_66,c_40,c_258,c_110,c_6016])).

tff(c_6051,plain,
    ( v3_pre_topc('#skF_3','#skF_4')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_6020])).

tff(c_6059,plain,(
    v3_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_34,c_6051])).

tff(c_6061,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_6059])).

%------------------------------------------------------------------------------
