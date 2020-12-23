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

% Result     : Theorem 2.98s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 281 expanded)
%              Number of leaves         :   44 ( 112 expanded)
%              Depth                    :   16
%              Number of atoms          :  180 ( 797 expanded)
%              Number of equality atoms :   35 ( 126 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_relat_1 > k3_subset_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_139,negated_conjecture,(
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

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_64,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_65,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_30,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_32,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ! [C] :
              ( m1_subset_1(C,A)
             => ( ~ r2_hidden(C,B)
               => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_111,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(c_46,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_74,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_34,plain,(
    ! [A_26] :
      ( v4_pre_topc(k2_struct_0(A_26),A_26)
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_75,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2])).

tff(c_22,plain,(
    ! [A_19] : k9_relat_1(k1_xboole_0,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_66,plain,(
    ! [A_19] : k9_relat_1('#skF_4',A_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_22])).

tff(c_24,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_65,plain,(
    k6_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_24])).

tff(c_32,plain,(
    ! [A_25] :
      ( l1_struct_0(A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_120,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_126,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_32,c_120])).

tff(c_130,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_126])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_131,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_50])).

tff(c_16,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,(
    ! [A_8] : m1_subset_1('#skF_4',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_16])).

tff(c_6,plain,(
    ! [A_2] : k1_subset_1(A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_72,plain,(
    ! [A_2] : k1_subset_1(A_2) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = k2_subset_1(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_70,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_73,plain,(
    ! [A_7] : k3_subset_1(A_7,'#skF_4') = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70])).

tff(c_18,plain,(
    ! [C_15,A_9,B_13] :
      ( r2_hidden(C_15,k3_subset_1(A_9,B_13))
      | r2_hidden(C_15,B_13)
      | ~ m1_subset_1(C_15,A_9)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_9))
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_511,plain,(
    ! [C_85,A_86,B_87] :
      ( r2_hidden(C_85,k3_subset_1(A_86,B_87))
      | r2_hidden(C_85,B_87)
      | ~ m1_subset_1(C_85,A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86))
      | A_86 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_18])).

tff(c_523,plain,(
    ! [C_85,A_7] :
      ( r2_hidden(C_85,A_7)
      | r2_hidden(C_85,'#skF_4')
      | ~ m1_subset_1(C_85,A_7)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_7))
      | A_7 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_511])).

tff(c_553,plain,(
    ! [C_88,A_89] :
      ( r2_hidden(C_88,A_89)
      | r2_hidden(C_88,'#skF_4')
      | ~ m1_subset_1(C_88,A_89)
      | A_89 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_523])).

tff(c_28,plain,(
    ! [B_23,A_22] :
      ( ~ r1_tarski(B_23,A_22)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_588,plain,(
    ! [C_88,A_89] :
      ( ~ r1_tarski('#skF_4',C_88)
      | r2_hidden(C_88,A_89)
      | ~ m1_subset_1(C_88,A_89)
      | A_89 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_553,c_28])).

tff(c_600,plain,(
    ! [C_88,A_89] :
      ( r2_hidden(C_88,A_89)
      | ~ m1_subset_1(C_88,A_89)
      | A_89 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_588])).

tff(c_36,plain,(
    ! [A_27] :
      ( v3_pre_topc(k2_struct_0(A_27),A_27)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_71,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_60,plain,(
    ! [D_41] :
      ( r2_hidden('#skF_3',D_41)
      | ~ r2_hidden(D_41,'#skF_4')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_137,plain,(
    ! [D_54] :
      ( r2_hidden('#skF_3',D_54)
      | ~ r2_hidden(D_54,'#skF_4')
      | ~ m1_subset_1(D_54,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_60])).

tff(c_146,plain,
    ( r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_71,c_137])).

tff(c_152,plain,(
    ~ r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_58,plain,(
    ! [D_41] :
      ( r2_hidden(D_41,'#skF_4')
      | ~ r2_hidden('#skF_3',D_41)
      | ~ v4_pre_topc(D_41,'#skF_2')
      | ~ v3_pre_topc(D_41,'#skF_2')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_297,plain,(
    ! [D_77] :
      ( r2_hidden(D_77,'#skF_4')
      | ~ r2_hidden('#skF_3',D_77)
      | ~ v4_pre_topc(D_77,'#skF_2')
      | ~ v3_pre_topc(D_77,'#skF_2')
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_58])).

tff(c_304,plain,
    ( r2_hidden(k2_struct_0('#skF_2'),'#skF_4')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_71,c_297])).

tff(c_314,plain,
    ( ~ r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_304])).

tff(c_601,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_314])).

tff(c_604,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_601])).

tff(c_608,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_604])).

tff(c_609,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_314])).

tff(c_656,plain,(
    ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_609])).

tff(c_665,plain,
    ( ~ m1_subset_1('#skF_3',k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_600,c_656])).

tff(c_668,plain,(
    k2_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_665])).

tff(c_256,plain,(
    ! [A_76] :
      ( m1_subset_1('#skF_1'(A_76),k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_266,plain,
    ( m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_256])).

tff(c_271,plain,
    ( m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_266])).

tff(c_272,plain,(
    m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_271])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( k9_relat_1(k6_relat_1(A_20),B_21) = B_21
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_293,plain,(
    k9_relat_1(k6_relat_1(k2_struct_0('#skF_2')),'#skF_1'('#skF_2')) = '#skF_1'('#skF_2') ),
    inference(resolution,[status(thm)],[c_272,c_26])).

tff(c_673,plain,(
    k9_relat_1(k6_relat_1('#skF_4'),'#skF_1'('#skF_2')) = '#skF_1'('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_293])).

tff(c_683,plain,(
    '#skF_1'('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_65,c_673])).

tff(c_42,plain,(
    ! [A_28] :
      ( ~ v1_xboole_0('#skF_1'(A_28))
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_714,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_683,c_42])).

tff(c_730,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_75,c_714])).

tff(c_732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_730])).

tff(c_733,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_609])).

tff(c_785,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_733])).

tff(c_789,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_785])).

tff(c_791,plain,(
    r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_807,plain,(
    ~ r1_tarski('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_791,c_28])).

tff(c_811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_807])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.46  
% 2.98/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.47  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_relat_1 > k3_subset_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.98/1.47  
% 2.98/1.47  %Foreground sorts:
% 2.98/1.47  
% 2.98/1.47  
% 2.98/1.47  %Background operators:
% 2.98/1.47  
% 2.98/1.47  
% 2.98/1.47  %Foreground operators:
% 2.98/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.98/1.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.98/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.98/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.98/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.98/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.47  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.98/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.47  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.98/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.98/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.98/1.47  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.98/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.98/1.47  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.98/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.47  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.98/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.98/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.98/1.47  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.98/1.47  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.98/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.98/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.98/1.47  
% 3.07/1.48  tff(f_139, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 3.07/1.48  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.07/1.48  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 3.07/1.48  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.07/1.48  tff(f_64, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 3.07/1.48  tff(f_65, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 3.07/1.48  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.07/1.48  tff(f_78, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.07/1.48  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.07/1.48  tff(f_30, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.07/1.48  tff(f_32, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.07/1.48  tff(f_40, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 3.07/1.48  tff(f_56, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 3.07/1.48  tff(f_74, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.07/1.48  tff(f_94, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 3.07/1.48  tff(f_34, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.07/1.48  tff(f_111, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_tops_1)).
% 3.07/1.48  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 3.07/1.48  tff(c_46, plain, (k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.07/1.48  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.07/1.48  tff(c_74, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4])).
% 3.07/1.48  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.07/1.48  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.07/1.48  tff(c_34, plain, (![A_26]: (v4_pre_topc(k2_struct_0(A_26), A_26) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.07/1.48  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.07/1.48  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.07/1.48  tff(c_75, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2])).
% 3.07/1.48  tff(c_22, plain, (![A_19]: (k9_relat_1(k1_xboole_0, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.07/1.48  tff(c_66, plain, (![A_19]: (k9_relat_1('#skF_4', A_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_22])).
% 3.07/1.48  tff(c_24, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.07/1.48  tff(c_65, plain, (k6_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_24])).
% 3.07/1.48  tff(c_32, plain, (![A_25]: (l1_struct_0(A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.07/1.48  tff(c_120, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.07/1.48  tff(c_126, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_32, c_120])).
% 3.07/1.48  tff(c_130, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_126])).
% 3.07/1.48  tff(c_50, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.07/1.48  tff(c_131, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_50])).
% 3.07/1.48  tff(c_16, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.07/1.48  tff(c_68, plain, (![A_8]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_16])).
% 3.07/1.48  tff(c_6, plain, (![A_2]: (k1_subset_1(A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.07/1.48  tff(c_72, plain, (![A_2]: (k1_subset_1(A_2)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6])).
% 3.07/1.48  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.07/1.48  tff(c_14, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=k2_subset_1(A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.07/1.48  tff(c_70, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 3.07/1.48  tff(c_73, plain, (![A_7]: (k3_subset_1(A_7, '#skF_4')=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70])).
% 3.07/1.48  tff(c_18, plain, (![C_15, A_9, B_13]: (r2_hidden(C_15, k3_subset_1(A_9, B_13)) | r2_hidden(C_15, B_13) | ~m1_subset_1(C_15, A_9) | ~m1_subset_1(B_13, k1_zfmisc_1(A_9)) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.07/1.48  tff(c_511, plain, (![C_85, A_86, B_87]: (r2_hidden(C_85, k3_subset_1(A_86, B_87)) | r2_hidden(C_85, B_87) | ~m1_subset_1(C_85, A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)) | A_86='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_18])).
% 3.07/1.48  tff(c_523, plain, (![C_85, A_7]: (r2_hidden(C_85, A_7) | r2_hidden(C_85, '#skF_4') | ~m1_subset_1(C_85, A_7) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_7)) | A_7='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_73, c_511])).
% 3.07/1.48  tff(c_553, plain, (![C_88, A_89]: (r2_hidden(C_88, A_89) | r2_hidden(C_88, '#skF_4') | ~m1_subset_1(C_88, A_89) | A_89='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_523])).
% 3.07/1.48  tff(c_28, plain, (![B_23, A_22]: (~r1_tarski(B_23, A_22) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.07/1.48  tff(c_588, plain, (![C_88, A_89]: (~r1_tarski('#skF_4', C_88) | r2_hidden(C_88, A_89) | ~m1_subset_1(C_88, A_89) | A_89='#skF_4')), inference(resolution, [status(thm)], [c_553, c_28])).
% 3.07/1.48  tff(c_600, plain, (![C_88, A_89]: (r2_hidden(C_88, A_89) | ~m1_subset_1(C_88, A_89) | A_89='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_588])).
% 3.07/1.48  tff(c_36, plain, (![A_27]: (v3_pre_topc(k2_struct_0(A_27), A_27) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.07/1.48  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.07/1.48  tff(c_71, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 3.07/1.48  tff(c_60, plain, (![D_41]: (r2_hidden('#skF_3', D_41) | ~r2_hidden(D_41, '#skF_4') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.07/1.48  tff(c_137, plain, (![D_54]: (r2_hidden('#skF_3', D_54) | ~r2_hidden(D_54, '#skF_4') | ~m1_subset_1(D_54, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_60])).
% 3.07/1.48  tff(c_146, plain, (r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_71, c_137])).
% 3.07/1.48  tff(c_152, plain, (~r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_146])).
% 3.07/1.48  tff(c_58, plain, (![D_41]: (r2_hidden(D_41, '#skF_4') | ~r2_hidden('#skF_3', D_41) | ~v4_pre_topc(D_41, '#skF_2') | ~v3_pre_topc(D_41, '#skF_2') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.07/1.48  tff(c_297, plain, (![D_77]: (r2_hidden(D_77, '#skF_4') | ~r2_hidden('#skF_3', D_77) | ~v4_pre_topc(D_77, '#skF_2') | ~v3_pre_topc(D_77, '#skF_2') | ~m1_subset_1(D_77, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_58])).
% 3.07/1.48  tff(c_304, plain, (r2_hidden(k2_struct_0('#skF_2'), '#skF_4') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_71, c_297])).
% 3.07/1.48  tff(c_314, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_152, c_304])).
% 3.07/1.48  tff(c_601, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_314])).
% 3.07/1.48  tff(c_604, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_601])).
% 3.07/1.48  tff(c_608, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_604])).
% 3.07/1.48  tff(c_609, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_314])).
% 3.07/1.48  tff(c_656, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_609])).
% 3.07/1.48  tff(c_665, plain, (~m1_subset_1('#skF_3', k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_600, c_656])).
% 3.07/1.48  tff(c_668, plain, (k2_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_665])).
% 3.07/1.48  tff(c_256, plain, (![A_76]: (m1_subset_1('#skF_1'(A_76), k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.07/1.48  tff(c_266, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_130, c_256])).
% 3.07/1.48  tff(c_271, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_266])).
% 3.07/1.48  tff(c_272, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_271])).
% 3.07/1.48  tff(c_26, plain, (![A_20, B_21]: (k9_relat_1(k6_relat_1(A_20), B_21)=B_21 | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.07/1.48  tff(c_293, plain, (k9_relat_1(k6_relat_1(k2_struct_0('#skF_2')), '#skF_1'('#skF_2'))='#skF_1'('#skF_2')), inference(resolution, [status(thm)], [c_272, c_26])).
% 3.07/1.48  tff(c_673, plain, (k9_relat_1(k6_relat_1('#skF_4'), '#skF_1'('#skF_2'))='#skF_1'('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_668, c_293])).
% 3.07/1.48  tff(c_683, plain, ('#skF_1'('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_65, c_673])).
% 3.07/1.48  tff(c_42, plain, (![A_28]: (~v1_xboole_0('#skF_1'(A_28)) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.07/1.48  tff(c_714, plain, (~v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_683, c_42])).
% 3.07/1.48  tff(c_730, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_75, c_714])).
% 3.07/1.48  tff(c_732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_730])).
% 3.07/1.48  tff(c_733, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_609])).
% 3.07/1.48  tff(c_785, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_733])).
% 3.07/1.48  tff(c_789, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_785])).
% 3.07/1.48  tff(c_791, plain, (r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(splitRight, [status(thm)], [c_146])).
% 3.07/1.48  tff(c_807, plain, (~r1_tarski('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_791, c_28])).
% 3.07/1.48  tff(c_811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_807])).
% 3.07/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.48  
% 3.07/1.48  Inference rules
% 3.07/1.48  ----------------------
% 3.07/1.48  #Ref     : 0
% 3.07/1.48  #Sup     : 137
% 3.07/1.48  #Fact    : 4
% 3.07/1.48  #Define  : 0
% 3.07/1.48  #Split   : 14
% 3.07/1.48  #Chain   : 0
% 3.07/1.48  #Close   : 0
% 3.07/1.48  
% 3.07/1.48  Ordering : KBO
% 3.07/1.48  
% 3.07/1.48  Simplification rules
% 3.07/1.48  ----------------------
% 3.07/1.48  #Subsume      : 13
% 3.07/1.48  #Demod        : 123
% 3.07/1.48  #Tautology    : 65
% 3.07/1.48  #SimpNegUnit  : 16
% 3.07/1.48  #BackRed      : 33
% 3.07/1.48  
% 3.07/1.48  #Partial instantiations: 0
% 3.07/1.48  #Strategies tried      : 1
% 3.07/1.48  
% 3.07/1.48  Timing (in seconds)
% 3.07/1.48  ----------------------
% 3.07/1.49  Preprocessing        : 0.34
% 3.07/1.49  Parsing              : 0.19
% 3.07/1.49  CNF conversion       : 0.02
% 3.07/1.49  Main loop            : 0.33
% 3.07/1.49  Inferencing          : 0.12
% 3.07/1.49  Reduction            : 0.10
% 3.07/1.49  Demodulation         : 0.07
% 3.07/1.49  BG Simplification    : 0.02
% 3.07/1.49  Subsumption          : 0.06
% 3.07/1.49  Abstraction          : 0.02
% 3.07/1.49  MUC search           : 0.00
% 3.07/1.49  Cooper               : 0.00
% 3.07/1.49  Total                : 0.71
% 3.07/1.49  Index Insertion      : 0.00
% 3.07/1.49  Index Deletion       : 0.00
% 3.07/1.49  Index Matching       : 0.00
% 3.07/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
