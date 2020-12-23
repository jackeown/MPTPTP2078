%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:39 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 278 expanded)
%              Number of leaves         :   33 ( 110 expanded)
%              Depth                    :   11
%              Number of atoms          :  137 ( 646 expanded)
%              Number of equality atoms :   41 ( 162 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v1_tops_1(B,A)
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( v3_pre_topc(C,A)
                   => k2_pre_topc(A,C) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),C,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( v3_pre_topc(B,A)
               => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C))) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_28,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_52,plain,(
    ! [A_40] :
      ( u1_struct_0(A_40) = k2_struct_0(A_40)
      | ~ l1_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_57,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = k2_struct_0(A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(resolution,[status(thm)],[c_28,c_52])).

tff(c_61,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_57])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_44])).

tff(c_92,plain,(
    ! [A_54,B_55,C_56] :
      ( k9_subset_1(A_54,B_55,C_56) = k3_xboole_0(B_55,C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_97,plain,(
    ! [B_55] : k9_subset_1(k2_struct_0('#skF_3'),B_55,'#skF_4') = k3_xboole_0(B_55,'#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_92])).

tff(c_130,plain,(
    ! [A_62,C_63,B_64] :
      ( k9_subset_1(A_62,C_63,B_64) = k9_subset_1(A_62,B_64,C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_132,plain,(
    ! [B_64] : k9_subset_1(k2_struct_0('#skF_3'),B_64,'#skF_4') = k9_subset_1(k2_struct_0('#skF_3'),'#skF_4',B_64) ),
    inference(resolution,[status(thm)],[c_64,c_130])).

tff(c_139,plain,(
    ! [B_65] : k9_subset_1(k2_struct_0('#skF_3'),'#skF_4',B_65) = k3_xboole_0(B_65,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_132])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_63,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_40])).

tff(c_98,plain,(
    ! [B_55] : k9_subset_1(k2_struct_0('#skF_3'),B_55,'#skF_5') = k3_xboole_0(B_55,'#skF_5') ),
    inference(resolution,[status(thm)],[c_63,c_92])).

tff(c_146,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_98])).

tff(c_36,plain,(
    k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_4')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_62,plain,(
    k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),'#skF_5','#skF_4')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_36])).

tff(c_99,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_5','#skF_4')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_62])).

tff(c_166,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_4','#skF_5')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_99])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_88,plain,(
    ! [C_51,A_52,B_53] :
      ( r2_hidden(C_51,A_52)
      | ~ r2_hidden(C_51,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_201,plain,(
    ! [A_67,B_68,A_69] :
      ( r2_hidden('#skF_1'(A_67,B_68),A_69)
      | ~ m1_subset_1(A_67,k1_zfmisc_1(A_69))
      | r1_tarski(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_6,c_88])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_213,plain,(
    ! [A_70,A_71] :
      ( ~ m1_subset_1(A_70,k1_zfmisc_1(A_71))
      | r1_tarski(A_70,A_71) ) ),
    inference(resolution,[status(thm)],[c_201,c_4])).

tff(c_221,plain,(
    r1_tarski('#skF_5',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_63,c_213])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_549,plain,(
    ! [A_114,B_115,C_116] :
      ( r1_tarski('#skF_2'(A_114,B_115,C_116),C_116)
      | k3_xboole_0(B_115,C_116) = A_114
      | ~ r1_tarski(A_114,C_116)
      | ~ r1_tarski(A_114,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r1_tarski('#skF_2'(A_8,B_9,C_10),A_8)
      | k3_xboole_0(B_9,C_10) = A_8
      | ~ r1_tarski(A_8,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_555,plain,(
    ! [B_115,C_116] :
      ( k3_xboole_0(B_115,C_116) = C_116
      | ~ r1_tarski(C_116,C_116)
      | ~ r1_tarski(C_116,B_115) ) ),
    inference(resolution,[status(thm)],[c_549,c_14])).

tff(c_566,plain,(
    ! [B_117,C_118] :
      ( k3_xboole_0(B_117,C_118) = C_118
      | ~ r1_tarski(C_118,B_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_555])).

tff(c_596,plain,(
    k3_xboole_0(k2_struct_0('#skF_3'),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_221,c_566])).

tff(c_42,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_269,plain,(
    ! [A_81,B_82] :
      ( k2_pre_topc(A_81,B_82) = k2_struct_0(A_81)
      | ~ v1_tops_1(B_82,A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_272,plain,(
    ! [B_82] :
      ( k2_pre_topc('#skF_3',B_82) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_82,'#skF_3')
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_269])).

tff(c_305,plain,(
    ! [B_87] :
      ( k2_pre_topc('#skF_3',B_87) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_87,'#skF_3')
      | ~ m1_subset_1(B_87,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_272])).

tff(c_308,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_305])).

tff(c_314,plain,(
    k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_308])).

tff(c_38,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_134,plain,(
    ! [B_64] : k9_subset_1(k2_struct_0('#skF_3'),B_64,'#skF_5') = k9_subset_1(k2_struct_0('#skF_3'),'#skF_5',B_64) ),
    inference(resolution,[status(thm)],[c_63,c_130])).

tff(c_138,plain,(
    ! [B_64] : k9_subset_1(k2_struct_0('#skF_3'),'#skF_5',B_64) = k3_xboole_0(B_64,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_134])).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_928,plain,(
    ! [A_141,B_142,C_143] :
      ( k2_pre_topc(A_141,k9_subset_1(u1_struct_0(A_141),B_142,k2_pre_topc(A_141,C_143))) = k2_pre_topc(A_141,k9_subset_1(u1_struct_0(A_141),B_142,C_143))
      | ~ v3_pre_topc(B_142,A_141)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_946,plain,(
    ! [B_142,C_143] :
      ( k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),B_142,k2_pre_topc('#skF_3',C_143))) = k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_142,C_143))
      | ~ v3_pre_topc(B_142,'#skF_3')
      | ~ m1_subset_1(C_143,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_928])).

tff(c_1030,plain,(
    ! [B_152,C_153] :
      ( k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),B_152,k2_pre_topc('#skF_3',C_153))) = k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),B_152,C_153))
      | ~ v3_pre_topc(B_152,'#skF_3')
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_152,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_61,c_61,c_61,c_946])).

tff(c_1056,plain,(
    ! [C_153] :
      ( k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),'#skF_5',C_153)) = k2_pre_topc('#skF_3',k3_xboole_0(k2_pre_topc('#skF_3',C_153),'#skF_5'))
      | ~ v3_pre_topc('#skF_5','#skF_3')
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_1030])).

tff(c_1189,plain,(
    ! [C_187] :
      ( k2_pre_topc('#skF_3',k3_xboole_0(k2_pre_topc('#skF_3',C_187),'#skF_5')) = k2_pre_topc('#skF_3',k3_xboole_0(C_187,'#skF_5'))
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_38,c_138,c_1056])).

tff(c_1192,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0(k2_pre_topc('#skF_3','#skF_4'),'#skF_5')) = k2_pre_topc('#skF_3',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_1189])).

tff(c_1197,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_4','#skF_5')) = k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_314,c_1192])).

tff(c_1199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_1197])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:42:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.56  
% 3.39/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.56  %$ v3_pre_topc > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 3.39/1.56  
% 3.39/1.56  %Foreground sorts:
% 3.39/1.56  
% 3.39/1.56  
% 3.39/1.56  %Background operators:
% 3.39/1.56  
% 3.39/1.56  
% 3.39/1.56  %Foreground operators:
% 3.39/1.56  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.39/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.39/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.39/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.39/1.56  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.39/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.39/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.39/1.56  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.39/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.39/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.39/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.39/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.39/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.39/1.56  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.39/1.56  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.39/1.56  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.39/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.39/1.56  
% 3.75/1.58  tff(f_114, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tops_1)).
% 3.75/1.58  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.75/1.58  tff(f_70, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.75/1.58  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.75/1.58  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.75/1.58  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.75/1.58  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.75/1.58  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.75/1.58  tff(f_51, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 3.75/1.58  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 3.75/1.58  tff(f_97, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C))) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tops_1)).
% 3.75/1.58  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.75/1.58  tff(c_28, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.75/1.58  tff(c_52, plain, (![A_40]: (u1_struct_0(A_40)=k2_struct_0(A_40) | ~l1_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.75/1.58  tff(c_57, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_pre_topc(A_41))), inference(resolution, [status(thm)], [c_28, c_52])).
% 3.75/1.58  tff(c_61, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_57])).
% 3.75/1.58  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.75/1.58  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_44])).
% 3.75/1.58  tff(c_92, plain, (![A_54, B_55, C_56]: (k9_subset_1(A_54, B_55, C_56)=k3_xboole_0(B_55, C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.75/1.58  tff(c_97, plain, (![B_55]: (k9_subset_1(k2_struct_0('#skF_3'), B_55, '#skF_4')=k3_xboole_0(B_55, '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_92])).
% 3.75/1.58  tff(c_130, plain, (![A_62, C_63, B_64]: (k9_subset_1(A_62, C_63, B_64)=k9_subset_1(A_62, B_64, C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.75/1.58  tff(c_132, plain, (![B_64]: (k9_subset_1(k2_struct_0('#skF_3'), B_64, '#skF_4')=k9_subset_1(k2_struct_0('#skF_3'), '#skF_4', B_64))), inference(resolution, [status(thm)], [c_64, c_130])).
% 3.75/1.58  tff(c_139, plain, (![B_65]: (k9_subset_1(k2_struct_0('#skF_3'), '#skF_4', B_65)=k3_xboole_0(B_65, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_132])).
% 3.75/1.58  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.75/1.58  tff(c_63, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_40])).
% 3.75/1.58  tff(c_98, plain, (![B_55]: (k9_subset_1(k2_struct_0('#skF_3'), B_55, '#skF_5')=k3_xboole_0(B_55, '#skF_5'))), inference(resolution, [status(thm)], [c_63, c_92])).
% 3.75/1.58  tff(c_146, plain, (k3_xboole_0('#skF_5', '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_139, c_98])).
% 3.75/1.58  tff(c_36, plain, (k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_4'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.75/1.58  tff(c_62, plain, (k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), '#skF_5', '#skF_4'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_36])).
% 3.75/1.58  tff(c_99, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', '#skF_4'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_62])).
% 3.75/1.58  tff(c_166, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_99])).
% 3.75/1.58  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.75/1.58  tff(c_88, plain, (![C_51, A_52, B_53]: (r2_hidden(C_51, A_52) | ~r2_hidden(C_51, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.75/1.58  tff(c_201, plain, (![A_67, B_68, A_69]: (r2_hidden('#skF_1'(A_67, B_68), A_69) | ~m1_subset_1(A_67, k1_zfmisc_1(A_69)) | r1_tarski(A_67, B_68))), inference(resolution, [status(thm)], [c_6, c_88])).
% 3.75/1.58  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.75/1.58  tff(c_213, plain, (![A_70, A_71]: (~m1_subset_1(A_70, k1_zfmisc_1(A_71)) | r1_tarski(A_70, A_71))), inference(resolution, [status(thm)], [c_201, c_4])).
% 3.75/1.58  tff(c_221, plain, (r1_tarski('#skF_5', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_63, c_213])).
% 3.75/1.58  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.75/1.58  tff(c_549, plain, (![A_114, B_115, C_116]: (r1_tarski('#skF_2'(A_114, B_115, C_116), C_116) | k3_xboole_0(B_115, C_116)=A_114 | ~r1_tarski(A_114, C_116) | ~r1_tarski(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.75/1.58  tff(c_14, plain, (![A_8, B_9, C_10]: (~r1_tarski('#skF_2'(A_8, B_9, C_10), A_8) | k3_xboole_0(B_9, C_10)=A_8 | ~r1_tarski(A_8, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.75/1.58  tff(c_555, plain, (![B_115, C_116]: (k3_xboole_0(B_115, C_116)=C_116 | ~r1_tarski(C_116, C_116) | ~r1_tarski(C_116, B_115))), inference(resolution, [status(thm)], [c_549, c_14])).
% 3.75/1.58  tff(c_566, plain, (![B_117, C_118]: (k3_xboole_0(B_117, C_118)=C_118 | ~r1_tarski(C_118, B_117))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_555])).
% 3.75/1.58  tff(c_596, plain, (k3_xboole_0(k2_struct_0('#skF_3'), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_221, c_566])).
% 3.75/1.58  tff(c_42, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.75/1.58  tff(c_269, plain, (![A_81, B_82]: (k2_pre_topc(A_81, B_82)=k2_struct_0(A_81) | ~v1_tops_1(B_82, A_81) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.75/1.58  tff(c_272, plain, (![B_82]: (k2_pre_topc('#skF_3', B_82)=k2_struct_0('#skF_3') | ~v1_tops_1(B_82, '#skF_3') | ~m1_subset_1(B_82, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_269])).
% 3.75/1.58  tff(c_305, plain, (![B_87]: (k2_pre_topc('#skF_3', B_87)=k2_struct_0('#skF_3') | ~v1_tops_1(B_87, '#skF_3') | ~m1_subset_1(B_87, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_272])).
% 3.75/1.58  tff(c_308, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_305])).
% 3.75/1.58  tff(c_314, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_308])).
% 3.75/1.58  tff(c_38, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.75/1.58  tff(c_134, plain, (![B_64]: (k9_subset_1(k2_struct_0('#skF_3'), B_64, '#skF_5')=k9_subset_1(k2_struct_0('#skF_3'), '#skF_5', B_64))), inference(resolution, [status(thm)], [c_63, c_130])).
% 3.75/1.58  tff(c_138, plain, (![B_64]: (k9_subset_1(k2_struct_0('#skF_3'), '#skF_5', B_64)=k3_xboole_0(B_64, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_134])).
% 3.75/1.58  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.75/1.58  tff(c_928, plain, (![A_141, B_142, C_143]: (k2_pre_topc(A_141, k9_subset_1(u1_struct_0(A_141), B_142, k2_pre_topc(A_141, C_143)))=k2_pre_topc(A_141, k9_subset_1(u1_struct_0(A_141), B_142, C_143)) | ~v3_pre_topc(B_142, A_141) | ~m1_subset_1(C_143, k1_zfmisc_1(u1_struct_0(A_141))) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.75/1.58  tff(c_946, plain, (![B_142, C_143]: (k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), B_142, k2_pre_topc('#skF_3', C_143)))=k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_142, C_143)) | ~v3_pre_topc(B_142, '#skF_3') | ~m1_subset_1(C_143, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_928])).
% 3.75/1.58  tff(c_1030, plain, (![B_152, C_153]: (k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), B_152, k2_pre_topc('#skF_3', C_153)))=k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), B_152, C_153)) | ~v3_pre_topc(B_152, '#skF_3') | ~m1_subset_1(C_153, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_152, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_61, c_61, c_61, c_946])).
% 3.75/1.58  tff(c_1056, plain, (![C_153]: (k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), '#skF_5', C_153))=k2_pre_topc('#skF_3', k3_xboole_0(k2_pre_topc('#skF_3', C_153), '#skF_5')) | ~v3_pre_topc('#skF_5', '#skF_3') | ~m1_subset_1(C_153, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_138, c_1030])).
% 3.75/1.58  tff(c_1189, plain, (![C_187]: (k2_pre_topc('#skF_3', k3_xboole_0(k2_pre_topc('#skF_3', C_187), '#skF_5'))=k2_pre_topc('#skF_3', k3_xboole_0(C_187, '#skF_5')) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_38, c_138, c_1056])).
% 3.75/1.58  tff(c_1192, plain, (k2_pre_topc('#skF_3', k3_xboole_0(k2_pre_topc('#skF_3', '#skF_4'), '#skF_5'))=k2_pre_topc('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_64, c_1189])).
% 3.75/1.58  tff(c_1197, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_596, c_314, c_1192])).
% 3.75/1.58  tff(c_1199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_1197])).
% 3.75/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.58  
% 3.75/1.58  Inference rules
% 3.75/1.58  ----------------------
% 3.75/1.58  #Ref     : 0
% 3.75/1.58  #Sup     : 275
% 3.75/1.58  #Fact    : 0
% 3.75/1.58  #Define  : 0
% 3.75/1.58  #Split   : 5
% 3.75/1.58  #Chain   : 0
% 3.75/1.58  #Close   : 0
% 3.75/1.58  
% 3.75/1.58  Ordering : KBO
% 3.75/1.58  
% 3.75/1.58  Simplification rules
% 3.75/1.58  ----------------------
% 3.75/1.58  #Subsume      : 86
% 3.75/1.58  #Demod        : 63
% 3.75/1.58  #Tautology    : 75
% 3.75/1.58  #SimpNegUnit  : 2
% 3.75/1.58  #BackRed      : 5
% 3.75/1.58  
% 3.75/1.58  #Partial instantiations: 0
% 3.75/1.58  #Strategies tried      : 1
% 3.75/1.58  
% 3.75/1.58  Timing (in seconds)
% 3.75/1.58  ----------------------
% 3.75/1.58  Preprocessing        : 0.32
% 3.75/1.58  Parsing              : 0.17
% 3.83/1.58  CNF conversion       : 0.02
% 3.83/1.58  Main loop            : 0.49
% 3.83/1.58  Inferencing          : 0.17
% 3.83/1.58  Reduction            : 0.14
% 3.83/1.58  Demodulation         : 0.09
% 3.83/1.58  BG Simplification    : 0.02
% 3.83/1.58  Subsumption          : 0.13
% 3.83/1.58  Abstraction          : 0.02
% 3.83/1.58  MUC search           : 0.00
% 3.83/1.58  Cooper               : 0.00
% 3.83/1.58  Total                : 0.85
% 3.83/1.58  Index Insertion      : 0.00
% 3.83/1.58  Index Deletion       : 0.00
% 3.83/1.58  Index Matching       : 0.00
% 3.83/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
