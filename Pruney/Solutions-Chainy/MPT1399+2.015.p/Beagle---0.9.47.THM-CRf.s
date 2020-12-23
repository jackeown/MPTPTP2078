%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:20 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 882 expanded)
%              Number of leaves         :   39 ( 304 expanded)
%              Depth                    :   16
%              Number of atoms          :  249 (2514 expanded)
%              Number of equality atoms :   29 ( 440 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_133,negated_conjecture,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

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

tff(f_30,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_32,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ! [C] :
              ( m1_subset_1(C,A)
             => ( ~ r2_hidden(C,B)
               => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_36,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_62,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_63,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2])).

tff(c_14,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_56,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_14])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_26,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_98,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_104,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = k2_struct_0(A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_26,c_98])).

tff(c_108,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_104])).

tff(c_50,plain,(
    ! [D_40] :
      ( r2_hidden('#skF_2',D_40)
      | ~ r2_hidden(D_40,'#skF_3')
      | ~ m1_subset_1(D_40,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_119,plain,(
    ! [D_53] :
      ( r2_hidden('#skF_2',D_53)
      | ~ r2_hidden(D_53,'#skF_3')
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_50])).

tff(c_128,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_119])).

tff(c_145,plain,(
    ~ r2_hidden('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_6,plain,(
    ! [A_2] : k1_subset_1(A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_60,plain,(
    ! [A_2] : k1_subset_1(A_2) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_subset_1(A_5)) = k2_subset_1(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_58,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_subset_1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12])).

tff(c_61,plain,(
    ! [A_5] : k3_subset_1(A_5,'#skF_3') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58])).

tff(c_199,plain,(
    ! [B_66,A_67] :
      ( v4_pre_topc(B_66,A_67)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_67),B_66),A_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_206,plain,(
    ! [A_67] :
      ( v4_pre_topc('#skF_3',A_67)
      | ~ v3_pre_topc(u1_struct_0(A_67),A_67)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_199])).

tff(c_212,plain,(
    ! [A_69] :
      ( v4_pre_topc('#skF_3',A_69)
      | ~ v3_pre_topc(u1_struct_0(A_69),A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_206])).

tff(c_215,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_212])).

tff(c_217,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_215])).

tff(c_218,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_181,plain,(
    ! [B_64,A_65] :
      ( v4_pre_topc(B_64,A_65)
      | ~ v1_xboole_0(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_184,plain,(
    ! [B_64] :
      ( v4_pre_topc(B_64,'#skF_1')
      | ~ v1_xboole_0(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_181])).

tff(c_236,plain,(
    ! [B_71] :
      ( v4_pre_topc(B_71,'#skF_1')
      | ~ v1_xboole_0(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_184])).

tff(c_240,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_236])).

tff(c_247,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_240])).

tff(c_249,plain,(
    ! [A_72,B_73] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_72),B_73),A_72)
      | ~ v4_pre_topc(B_73,A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_259,plain,(
    ! [A_72] :
      ( v3_pre_topc(u1_struct_0(A_72),A_72)
      | ~ v4_pre_topc('#skF_3',A_72)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_249])).

tff(c_265,plain,(
    ! [A_74] :
      ( v3_pre_topc(u1_struct_0(A_74),A_74)
      | ~ v4_pre_topc('#skF_3',A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_259])).

tff(c_271,plain,
    ( v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_265])).

tff(c_274,plain,(
    v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_247,c_271])).

tff(c_276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_274])).

tff(c_277,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_48,plain,(
    ! [D_40] :
      ( r2_hidden(D_40,'#skF_3')
      | ~ r2_hidden('#skF_2',D_40)
      | ~ v4_pre_topc(D_40,'#skF_1')
      | ~ v3_pre_topc(D_40,'#skF_1')
      | ~ m1_subset_1(D_40,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_280,plain,(
    ! [D_75] :
      ( r2_hidden(D_75,'#skF_3')
      | ~ r2_hidden('#skF_2',D_75)
      | ~ v4_pre_topc(D_75,'#skF_1')
      | ~ v3_pre_topc(D_75,'#skF_1')
      | ~ m1_subset_1(D_75,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_48])).

tff(c_284,plain,
    ( r2_hidden('#skF_3','#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_280])).

tff(c_291,plain,
    ( r2_hidden('#skF_3','#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_284])).

tff(c_292,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_291])).

tff(c_297,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_292])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_109,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_40])).

tff(c_16,plain,(
    ! [C_13,A_7,B_11] :
      ( r2_hidden(C_13,k3_subset_1(A_7,B_11))
      | r2_hidden(C_13,B_11)
      | ~ m1_subset_1(C_13,A_7)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_7))
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_372,plain,(
    ! [C_83,A_84,B_85] :
      ( r2_hidden(C_83,k3_subset_1(A_84,B_85))
      | r2_hidden(C_83,B_85)
      | ~ m1_subset_1(C_83,A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84))
      | A_84 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_16])).

tff(c_381,plain,(
    ! [C_83,A_5] :
      ( r2_hidden(C_83,A_5)
      | r2_hidden(C_83,'#skF_3')
      | ~ m1_subset_1(C_83,A_5)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_5))
      | A_5 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_372])).

tff(c_402,plain,(
    ! [C_86,A_87] :
      ( r2_hidden(C_86,A_87)
      | r2_hidden(C_86,'#skF_3')
      | ~ m1_subset_1(C_86,A_87)
      | A_87 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_381])).

tff(c_30,plain,(
    ! [A_25] :
      ( v4_pre_topc(k2_struct_0(A_25),A_25)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_59,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_129,plain,
    ( r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_59,c_119])).

tff(c_147,plain,(
    ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_278,plain,(
    v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_288,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),'#skF_3')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_59,c_280])).

tff(c_295,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),'#skF_3')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_288])).

tff(c_296,plain,
    ( ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_295])).

tff(c_298,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_301,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_298])).

tff(c_305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_301])).

tff(c_306,plain,(
    ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_405,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1'))
    | k2_struct_0('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_402,c_306])).

tff(c_431,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | k2_struct_0('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_405])).

tff(c_441,plain,(
    k2_struct_0('#skF_1') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_431])).

tff(c_454,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_278])).

tff(c_464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_297,c_454])).

tff(c_465,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_431])).

tff(c_20,plain,(
    ! [B_18,A_17] :
      ( ~ r1_tarski(B_18,A_17)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_474,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_465,c_20])).

tff(c_480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_474])).

tff(c_481,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_292])).

tff(c_556,plain,(
    ! [C_98,A_99,B_100] :
      ( r2_hidden(C_98,k3_subset_1(A_99,B_100))
      | r2_hidden(C_98,B_100)
      | ~ m1_subset_1(C_98,A_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99))
      | A_99 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_16])).

tff(c_565,plain,(
    ! [C_98,A_5] :
      ( r2_hidden(C_98,A_5)
      | r2_hidden(C_98,'#skF_3')
      | ~ m1_subset_1(C_98,A_5)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_5))
      | A_5 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_556])).

tff(c_586,plain,(
    ! [C_101,A_102] :
      ( r2_hidden(C_101,A_102)
      | r2_hidden(C_101,'#skF_3')
      | ~ m1_subset_1(C_101,A_102)
      | A_102 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_565])).

tff(c_496,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_499,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_496])).

tff(c_503,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_499])).

tff(c_504,plain,(
    ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_589,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1'))
    | k2_struct_0('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_586,c_504])).

tff(c_619,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | k2_struct_0('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_589])).

tff(c_620,plain,(
    k2_struct_0('#skF_1') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_481,c_619])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_28,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(u1_struct_0(A_24))
      | ~ l1_struct_0(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_113,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_28])).

tff(c_116,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_113])).

tff(c_130,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_133,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_130])).

tff(c_137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_133])).

tff(c_138,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_641,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_138])).

tff(c_649,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_641])).

tff(c_651,plain,(
    r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_665,plain,(
    ~ r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_651,c_20])).

tff(c_669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_665])).

tff(c_670,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_674,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_670,c_20])).

tff(c_678,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_674])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:14:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.42  
% 2.90/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.42  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.90/1.42  
% 2.90/1.42  %Foreground sorts:
% 2.90/1.42  
% 2.90/1.42  
% 2.90/1.42  %Background operators:
% 2.90/1.42  
% 2.90/1.42  
% 2.90/1.42  %Foreground operators:
% 2.90/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.90/1.42  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.90/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.90/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.90/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.42  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.90/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.90/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.90/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.90/1.42  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.90/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.42  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.90/1.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.90/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.90/1.42  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.90/1.42  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.90/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.90/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.42  
% 2.90/1.44  tff(f_133, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.90/1.44  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.90/1.44  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.90/1.44  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.90/1.44  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.90/1.44  tff(f_78, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.90/1.44  tff(f_30, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.90/1.44  tff(f_32, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.90/1.44  tff(f_36, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 2.90/1.44  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 2.90/1.44  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.90/1.44  tff(f_52, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 2.90/1.44  tff(f_96, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.90/1.44  tff(f_34, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.90/1.44  tff(f_63, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.90/1.44  tff(f_90, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.90/1.44  tff(c_36, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.90/1.44  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.90/1.44  tff(c_62, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4])).
% 2.90/1.44  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.90/1.44  tff(c_63, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2])).
% 2.90/1.44  tff(c_14, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.90/1.44  tff(c_56, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_14])).
% 2.90/1.44  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.90/1.44  tff(c_26, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.90/1.44  tff(c_98, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.90/1.44  tff(c_104, plain, (![A_52]: (u1_struct_0(A_52)=k2_struct_0(A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_26, c_98])).
% 2.90/1.44  tff(c_108, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_104])).
% 2.90/1.44  tff(c_50, plain, (![D_40]: (r2_hidden('#skF_2', D_40) | ~r2_hidden(D_40, '#skF_3') | ~m1_subset_1(D_40, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.90/1.44  tff(c_119, plain, (![D_53]: (r2_hidden('#skF_2', D_53) | ~r2_hidden(D_53, '#skF_3') | ~m1_subset_1(D_53, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_50])).
% 2.90/1.44  tff(c_128, plain, (r2_hidden('#skF_2', '#skF_3') | ~r2_hidden('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_119])).
% 2.90/1.44  tff(c_145, plain, (~r2_hidden('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_128])).
% 2.90/1.44  tff(c_6, plain, (![A_2]: (k1_subset_1(A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.90/1.44  tff(c_60, plain, (![A_2]: (k1_subset_1(A_2)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6])).
% 2.90/1.44  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.90/1.44  tff(c_12, plain, (![A_5]: (k3_subset_1(A_5, k1_subset_1(A_5))=k2_subset_1(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.90/1.44  tff(c_58, plain, (![A_5]: (k3_subset_1(A_5, k1_subset_1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12])).
% 2.90/1.44  tff(c_61, plain, (![A_5]: (k3_subset_1(A_5, '#skF_3')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58])).
% 2.90/1.44  tff(c_199, plain, (![B_66, A_67]: (v4_pre_topc(B_66, A_67) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_67), B_66), A_67) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.90/1.44  tff(c_206, plain, (![A_67]: (v4_pre_topc('#skF_3', A_67) | ~v3_pre_topc(u1_struct_0(A_67), A_67) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(superposition, [status(thm), theory('equality')], [c_61, c_199])).
% 2.90/1.44  tff(c_212, plain, (![A_69]: (v4_pre_topc('#skF_3', A_69) | ~v3_pre_topc(u1_struct_0(A_69), A_69) | ~l1_pre_topc(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_206])).
% 2.90/1.44  tff(c_215, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_108, c_212])).
% 2.90/1.44  tff(c_217, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_215])).
% 2.90/1.44  tff(c_218, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_217])).
% 2.90/1.44  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.90/1.44  tff(c_181, plain, (![B_64, A_65]: (v4_pre_topc(B_64, A_65) | ~v1_xboole_0(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.90/1.44  tff(c_184, plain, (![B_64]: (v4_pre_topc(B_64, '#skF_1') | ~v1_xboole_0(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_108, c_181])).
% 2.90/1.44  tff(c_236, plain, (![B_71]: (v4_pre_topc(B_71, '#skF_1') | ~v1_xboole_0(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_184])).
% 2.90/1.44  tff(c_240, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_236])).
% 2.90/1.44  tff(c_247, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_240])).
% 2.90/1.44  tff(c_249, plain, (![A_72, B_73]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_72), B_73), A_72) | ~v4_pre_topc(B_73, A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.90/1.44  tff(c_259, plain, (![A_72]: (v3_pre_topc(u1_struct_0(A_72), A_72) | ~v4_pre_topc('#skF_3', A_72) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(superposition, [status(thm), theory('equality')], [c_61, c_249])).
% 2.90/1.44  tff(c_265, plain, (![A_74]: (v3_pre_topc(u1_struct_0(A_74), A_74) | ~v4_pre_topc('#skF_3', A_74) | ~l1_pre_topc(A_74))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_259])).
% 2.90/1.44  tff(c_271, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_108, c_265])).
% 2.90/1.44  tff(c_274, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_247, c_271])).
% 2.90/1.44  tff(c_276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_218, c_274])).
% 2.90/1.44  tff(c_277, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_217])).
% 2.90/1.44  tff(c_48, plain, (![D_40]: (r2_hidden(D_40, '#skF_3') | ~r2_hidden('#skF_2', D_40) | ~v4_pre_topc(D_40, '#skF_1') | ~v3_pre_topc(D_40, '#skF_1') | ~m1_subset_1(D_40, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.90/1.44  tff(c_280, plain, (![D_75]: (r2_hidden(D_75, '#skF_3') | ~r2_hidden('#skF_2', D_75) | ~v4_pre_topc(D_75, '#skF_1') | ~v3_pre_topc(D_75, '#skF_1') | ~m1_subset_1(D_75, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_48])).
% 2.90/1.44  tff(c_284, plain, (r2_hidden('#skF_3', '#skF_3') | ~r2_hidden('#skF_2', '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_280])).
% 2.90/1.44  tff(c_291, plain, (r2_hidden('#skF_3', '#skF_3') | ~r2_hidden('#skF_2', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_277, c_284])).
% 2.90/1.44  tff(c_292, plain, (~r2_hidden('#skF_2', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_145, c_291])).
% 2.90/1.44  tff(c_297, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_292])).
% 2.90/1.44  tff(c_40, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.90/1.44  tff(c_109, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_40])).
% 2.90/1.44  tff(c_16, plain, (![C_13, A_7, B_11]: (r2_hidden(C_13, k3_subset_1(A_7, B_11)) | r2_hidden(C_13, B_11) | ~m1_subset_1(C_13, A_7) | ~m1_subset_1(B_11, k1_zfmisc_1(A_7)) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.90/1.44  tff(c_372, plain, (![C_83, A_84, B_85]: (r2_hidden(C_83, k3_subset_1(A_84, B_85)) | r2_hidden(C_83, B_85) | ~m1_subset_1(C_83, A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)) | A_84='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_16])).
% 2.90/1.44  tff(c_381, plain, (![C_83, A_5]: (r2_hidden(C_83, A_5) | r2_hidden(C_83, '#skF_3') | ~m1_subset_1(C_83, A_5) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_5)) | A_5='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_61, c_372])).
% 2.90/1.44  tff(c_402, plain, (![C_86, A_87]: (r2_hidden(C_86, A_87) | r2_hidden(C_86, '#skF_3') | ~m1_subset_1(C_86, A_87) | A_87='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_381])).
% 2.90/1.44  tff(c_30, plain, (![A_25]: (v4_pre_topc(k2_struct_0(A_25), A_25) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.90/1.44  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.90/1.44  tff(c_59, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.90/1.44  tff(c_129, plain, (r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_59, c_119])).
% 2.90/1.44  tff(c_147, plain, (~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_129])).
% 2.90/1.44  tff(c_278, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_217])).
% 2.90/1.44  tff(c_288, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_59, c_280])).
% 2.90/1.44  tff(c_295, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_278, c_288])).
% 2.90/1.44  tff(c_296, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_147, c_295])).
% 2.90/1.44  tff(c_298, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_296])).
% 2.90/1.44  tff(c_301, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_298])).
% 2.90/1.44  tff(c_305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_301])).
% 2.90/1.44  tff(c_306, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_296])).
% 2.90/1.44  tff(c_405, plain, (r2_hidden('#skF_2', '#skF_3') | ~m1_subset_1('#skF_2', k2_struct_0('#skF_1')) | k2_struct_0('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_402, c_306])).
% 2.90/1.44  tff(c_431, plain, (r2_hidden('#skF_2', '#skF_3') | k2_struct_0('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_405])).
% 2.90/1.44  tff(c_441, plain, (k2_struct_0('#skF_1')='#skF_3'), inference(splitLeft, [status(thm)], [c_431])).
% 2.90/1.44  tff(c_454, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_441, c_278])).
% 2.90/1.44  tff(c_464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_297, c_454])).
% 2.90/1.44  tff(c_465, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_431])).
% 2.90/1.44  tff(c_20, plain, (![B_18, A_17]: (~r1_tarski(B_18, A_17) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.90/1.44  tff(c_474, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_465, c_20])).
% 2.90/1.44  tff(c_480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_474])).
% 2.90/1.44  tff(c_481, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_292])).
% 2.90/1.44  tff(c_556, plain, (![C_98, A_99, B_100]: (r2_hidden(C_98, k3_subset_1(A_99, B_100)) | r2_hidden(C_98, B_100) | ~m1_subset_1(C_98, A_99) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)) | A_99='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_16])).
% 2.90/1.44  tff(c_565, plain, (![C_98, A_5]: (r2_hidden(C_98, A_5) | r2_hidden(C_98, '#skF_3') | ~m1_subset_1(C_98, A_5) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_5)) | A_5='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_61, c_556])).
% 2.90/1.44  tff(c_586, plain, (![C_101, A_102]: (r2_hidden(C_101, A_102) | r2_hidden(C_101, '#skF_3') | ~m1_subset_1(C_101, A_102) | A_102='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_565])).
% 2.90/1.44  tff(c_496, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_296])).
% 2.90/1.44  tff(c_499, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_496])).
% 2.90/1.44  tff(c_503, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_499])).
% 2.90/1.44  tff(c_504, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_296])).
% 2.90/1.44  tff(c_589, plain, (r2_hidden('#skF_2', '#skF_3') | ~m1_subset_1('#skF_2', k2_struct_0('#skF_1')) | k2_struct_0('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_586, c_504])).
% 2.90/1.44  tff(c_619, plain, (r2_hidden('#skF_2', '#skF_3') | k2_struct_0('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_589])).
% 2.90/1.44  tff(c_620, plain, (k2_struct_0('#skF_1')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_481, c_619])).
% 2.90/1.44  tff(c_46, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.90/1.44  tff(c_28, plain, (![A_24]: (~v1_xboole_0(u1_struct_0(A_24)) | ~l1_struct_0(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.90/1.44  tff(c_113, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_108, c_28])).
% 2.90/1.44  tff(c_116, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_46, c_113])).
% 2.90/1.44  tff(c_130, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_116])).
% 2.90/1.44  tff(c_133, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_130])).
% 2.90/1.44  tff(c_137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_133])).
% 2.90/1.44  tff(c_138, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_116])).
% 2.90/1.44  tff(c_641, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_620, c_138])).
% 2.90/1.44  tff(c_649, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_641])).
% 2.90/1.44  tff(c_651, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_129])).
% 2.90/1.44  tff(c_665, plain, (~r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_651, c_20])).
% 2.90/1.44  tff(c_669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_665])).
% 2.90/1.44  tff(c_670, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_128])).
% 2.90/1.44  tff(c_674, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_670, c_20])).
% 2.90/1.44  tff(c_678, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_674])).
% 2.90/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.44  
% 2.90/1.44  Inference rules
% 2.90/1.44  ----------------------
% 2.90/1.44  #Ref     : 0
% 2.90/1.44  #Sup     : 96
% 2.90/1.44  #Fact    : 4
% 2.90/1.44  #Define  : 0
% 2.90/1.44  #Split   : 9
% 2.90/1.44  #Chain   : 0
% 2.90/1.44  #Close   : 0
% 2.90/1.44  
% 2.90/1.44  Ordering : KBO
% 2.90/1.44  
% 2.90/1.44  Simplification rules
% 2.90/1.44  ----------------------
% 2.90/1.44  #Subsume      : 11
% 2.90/1.44  #Demod        : 119
% 2.90/1.44  #Tautology    : 37
% 2.90/1.44  #SimpNegUnit  : 8
% 2.90/1.44  #BackRed      : 29
% 2.90/1.44  
% 2.90/1.44  #Partial instantiations: 0
% 2.90/1.44  #Strategies tried      : 1
% 2.90/1.44  
% 2.90/1.44  Timing (in seconds)
% 2.90/1.44  ----------------------
% 3.14/1.45  Preprocessing        : 0.34
% 3.14/1.45  Parsing              : 0.19
% 3.14/1.45  CNF conversion       : 0.02
% 3.14/1.45  Main loop            : 0.32
% 3.14/1.45  Inferencing          : 0.11
% 3.14/1.45  Reduction            : 0.10
% 3.14/1.45  Demodulation         : 0.07
% 3.14/1.45  BG Simplification    : 0.02
% 3.14/1.45  Subsumption          : 0.06
% 3.14/1.45  Abstraction          : 0.01
% 3.14/1.45  MUC search           : 0.00
% 3.14/1.45  Cooper               : 0.00
% 3.14/1.45  Total                : 0.70
% 3.14/1.45  Index Insertion      : 0.00
% 3.14/1.45  Index Deletion       : 0.00
% 3.14/1.45  Index Matching       : 0.00
% 3.14/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
