%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:01 EST 2020

% Result     : Theorem 8.20s
% Output     : CNFRefutation 8.26s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 170 expanded)
%              Number of leaves         :   36 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  120 ( 356 expanded)
%              Number of equality atoms :   18 (  65 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_107,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_38,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_89,axiom,(
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

tff(c_38,plain,(
    '#skF_6' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_36,plain,(
    ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_50,plain,(
    ~ v3_pre_topc('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_24,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_67,plain,(
    ! [A_63] :
      ( u1_struct_0(A_63) = k2_struct_0(A_63)
      | ~ l1_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_72,plain,(
    ! [A_64] :
      ( u1_struct_0(A_64) = k2_struct_0(A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_24,c_67])).

tff(c_76,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_72])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_77,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_46])).

tff(c_42,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_44,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_91,plain,(
    ! [B_67,A_68] :
      ( l1_pre_topc(B_67)
      | ~ m1_pre_topc(B_67,A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_94,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_91])).

tff(c_97,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_94])).

tff(c_71,plain,(
    ! [A_23] :
      ( u1_struct_0(A_23) = k2_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(resolution,[status(thm)],[c_24,c_67])).

tff(c_101,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_97,c_71])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_49,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40])).

tff(c_102,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_49])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_133,plain,(
    ! [C_80,A_81,B_82] :
      ( r2_hidden(C_80,A_81)
      | ~ r2_hidden(C_80,B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_283,plain,(
    ! [A_109,B_110,A_111] :
      ( r2_hidden('#skF_1'(A_109,B_110),A_111)
      | ~ m1_subset_1(A_109,k1_zfmisc_1(A_111))
      | r1_tarski(A_109,B_110) ) ),
    inference(resolution,[status(thm)],[c_6,c_133])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_320,plain,(
    ! [A_114,A_115] :
      ( ~ m1_subset_1(A_114,k1_zfmisc_1(A_115))
      | r1_tarski(A_114,A_115) ) ),
    inference(resolution,[status(thm)],[c_283,c_4])).

tff(c_350,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_102,c_320])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_357,plain,(
    k3_xboole_0('#skF_4',k2_struct_0('#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_350,c_8])).

tff(c_10,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_51,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_138,plain,(
    ! [A_86,B_87,C_88] :
      ( k9_subset_1(A_86,B_87,C_88) = k3_xboole_0(B_87,C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_151,plain,(
    ! [A_89,B_90] : k9_subset_1(A_89,B_90,A_89) = k3_xboole_0(B_90,A_89) ),
    inference(resolution,[status(thm)],[c_51,c_138])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( m1_subset_1(k9_subset_1(A_10,B_11,C_12),k1_zfmisc_1(A_10))
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_157,plain,(
    ! [B_90,A_89] :
      ( m1_subset_1(k3_xboole_0(B_90,A_89),k1_zfmisc_1(A_89))
      | ~ m1_subset_1(A_89,k1_zfmisc_1(A_89)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_14])).

tff(c_163,plain,(
    ! [B_90,A_89] : m1_subset_1(k3_xboole_0(B_90,A_89),k1_zfmisc_1(A_89)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_157])).

tff(c_150,plain,(
    ! [A_9,B_87] : k9_subset_1(A_9,B_87,A_9) = k3_xboole_0(B_87,A_9) ),
    inference(resolution,[status(thm)],[c_51,c_138])).

tff(c_1017,plain,(
    ! [B_152,D_153,A_154] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_152),D_153,k2_struct_0(B_152)),B_152)
      | ~ v3_pre_topc(D_153,A_154)
      | ~ m1_subset_1(D_153,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_152),D_153,k2_struct_0(B_152)),k1_zfmisc_1(u1_struct_0(B_152)))
      | ~ m1_pre_topc(B_152,A_154)
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1032,plain,(
    ! [B_152,D_153] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_152),D_153,k2_struct_0(B_152)),B_152)
      | ~ v3_pre_topc(D_153,'#skF_3')
      | ~ m1_subset_1(D_153,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_152),D_153,k2_struct_0(B_152)),k1_zfmisc_1(u1_struct_0(B_152)))
      | ~ m1_pre_topc(B_152,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_1017])).

tff(c_12086,plain,(
    ! [B_556,D_557] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_556),D_557,k2_struct_0(B_556)),B_556)
      | ~ v3_pre_topc(D_557,'#skF_3')
      | ~ m1_subset_1(D_557,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_556),D_557,k2_struct_0(B_556)),k1_zfmisc_1(u1_struct_0(B_556)))
      | ~ m1_pre_topc(B_556,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1032])).

tff(c_12096,plain,(
    ! [D_557] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0('#skF_5'),D_557,k2_struct_0('#skF_5')),'#skF_5')
      | ~ v3_pre_topc(D_557,'#skF_3')
      | ~ m1_subset_1(D_557,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(k9_subset_1(k2_struct_0('#skF_5'),D_557,k2_struct_0('#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_12086])).

tff(c_12115,plain,(
    ! [D_558] :
      ( v3_pre_topc(k3_xboole_0(D_558,k2_struct_0('#skF_5')),'#skF_5')
      | ~ v3_pre_topc(D_558,'#skF_3')
      | ~ m1_subset_1(D_558,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_163,c_150,c_101,c_150,c_101,c_12096])).

tff(c_12138,plain,
    ( v3_pre_topc('#skF_4','#skF_5')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_12115])).

tff(c_12148,plain,(
    v3_pre_topc('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_42,c_12138])).

tff(c_12150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_12148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:09:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.20/3.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.26/3.20  
% 8.26/3.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.26/3.20  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 8.26/3.20  
% 8.26/3.20  %Foreground sorts:
% 8.26/3.20  
% 8.26/3.20  
% 8.26/3.20  %Background operators:
% 8.26/3.20  
% 8.26/3.20  
% 8.26/3.20  %Foreground operators:
% 8.26/3.20  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 8.26/3.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.26/3.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.26/3.20  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.26/3.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.26/3.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.26/3.20  tff('#skF_5', type, '#skF_5': $i).
% 8.26/3.20  tff('#skF_6', type, '#skF_6': $i).
% 8.26/3.20  tff('#skF_3', type, '#skF_3': $i).
% 8.26/3.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.26/3.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.26/3.20  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.26/3.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.26/3.20  tff('#skF_4', type, '#skF_4': $i).
% 8.26/3.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.26/3.20  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.26/3.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.26/3.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.26/3.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.26/3.20  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.26/3.20  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 8.26/3.20  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.26/3.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.26/3.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.26/3.20  
% 8.26/3.22  tff(f_107, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 8.26/3.22  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.26/3.22  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 8.26/3.22  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 8.26/3.22  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.26/3.22  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 8.26/3.22  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.26/3.22  tff(f_38, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 8.26/3.22  tff(f_40, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 8.26/3.22  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.26/3.22  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 8.26/3.22  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (v3_pre_topc(C, B) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & (k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)) = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_tops_2)).
% 8.26/3.22  tff(c_38, plain, ('#skF_6'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.26/3.22  tff(c_36, plain, (~v3_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.26/3.22  tff(c_50, plain, (~v3_pre_topc('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36])).
% 8.26/3.22  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.26/3.22  tff(c_24, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.26/3.22  tff(c_67, plain, (![A_63]: (u1_struct_0(A_63)=k2_struct_0(A_63) | ~l1_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.26/3.22  tff(c_72, plain, (![A_64]: (u1_struct_0(A_64)=k2_struct_0(A_64) | ~l1_pre_topc(A_64))), inference(resolution, [status(thm)], [c_24, c_67])).
% 8.26/3.22  tff(c_76, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_72])).
% 8.26/3.22  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.26/3.22  tff(c_77, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_46])).
% 8.26/3.22  tff(c_42, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.26/3.22  tff(c_44, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.26/3.22  tff(c_91, plain, (![B_67, A_68]: (l1_pre_topc(B_67) | ~m1_pre_topc(B_67, A_68) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.26/3.22  tff(c_94, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_91])).
% 8.26/3.22  tff(c_97, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_94])).
% 8.26/3.22  tff(c_71, plain, (![A_23]: (u1_struct_0(A_23)=k2_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(resolution, [status(thm)], [c_24, c_67])).
% 8.26/3.22  tff(c_101, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_97, c_71])).
% 8.26/3.22  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.26/3.22  tff(c_49, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40])).
% 8.26/3.22  tff(c_102, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_49])).
% 8.26/3.22  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.26/3.22  tff(c_133, plain, (![C_80, A_81, B_82]: (r2_hidden(C_80, A_81) | ~r2_hidden(C_80, B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.26/3.22  tff(c_283, plain, (![A_109, B_110, A_111]: (r2_hidden('#skF_1'(A_109, B_110), A_111) | ~m1_subset_1(A_109, k1_zfmisc_1(A_111)) | r1_tarski(A_109, B_110))), inference(resolution, [status(thm)], [c_6, c_133])).
% 8.26/3.22  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.26/3.22  tff(c_320, plain, (![A_114, A_115]: (~m1_subset_1(A_114, k1_zfmisc_1(A_115)) | r1_tarski(A_114, A_115))), inference(resolution, [status(thm)], [c_283, c_4])).
% 8.26/3.22  tff(c_350, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_102, c_320])).
% 8.26/3.22  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.26/3.22  tff(c_357, plain, (k3_xboole_0('#skF_4', k2_struct_0('#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_350, c_8])).
% 8.26/3.22  tff(c_10, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.26/3.22  tff(c_12, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.26/3.22  tff(c_51, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 8.26/3.22  tff(c_138, plain, (![A_86, B_87, C_88]: (k9_subset_1(A_86, B_87, C_88)=k3_xboole_0(B_87, C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.26/3.22  tff(c_151, plain, (![A_89, B_90]: (k9_subset_1(A_89, B_90, A_89)=k3_xboole_0(B_90, A_89))), inference(resolution, [status(thm)], [c_51, c_138])).
% 8.26/3.22  tff(c_14, plain, (![A_10, B_11, C_12]: (m1_subset_1(k9_subset_1(A_10, B_11, C_12), k1_zfmisc_1(A_10)) | ~m1_subset_1(C_12, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.26/3.22  tff(c_157, plain, (![B_90, A_89]: (m1_subset_1(k3_xboole_0(B_90, A_89), k1_zfmisc_1(A_89)) | ~m1_subset_1(A_89, k1_zfmisc_1(A_89)))), inference(superposition, [status(thm), theory('equality')], [c_151, c_14])).
% 8.26/3.22  tff(c_163, plain, (![B_90, A_89]: (m1_subset_1(k3_xboole_0(B_90, A_89), k1_zfmisc_1(A_89)))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_157])).
% 8.26/3.22  tff(c_150, plain, (![A_9, B_87]: (k9_subset_1(A_9, B_87, A_9)=k3_xboole_0(B_87, A_9))), inference(resolution, [status(thm)], [c_51, c_138])).
% 8.26/3.22  tff(c_1017, plain, (![B_152, D_153, A_154]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_152), D_153, k2_struct_0(B_152)), B_152) | ~v3_pre_topc(D_153, A_154) | ~m1_subset_1(D_153, k1_zfmisc_1(u1_struct_0(A_154))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_152), D_153, k2_struct_0(B_152)), k1_zfmisc_1(u1_struct_0(B_152))) | ~m1_pre_topc(B_152, A_154) | ~l1_pre_topc(A_154))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.26/3.22  tff(c_1032, plain, (![B_152, D_153]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_152), D_153, k2_struct_0(B_152)), B_152) | ~v3_pre_topc(D_153, '#skF_3') | ~m1_subset_1(D_153, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_152), D_153, k2_struct_0(B_152)), k1_zfmisc_1(u1_struct_0(B_152))) | ~m1_pre_topc(B_152, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_1017])).
% 8.26/3.22  tff(c_12086, plain, (![B_556, D_557]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_556), D_557, k2_struct_0(B_556)), B_556) | ~v3_pre_topc(D_557, '#skF_3') | ~m1_subset_1(D_557, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_556), D_557, k2_struct_0(B_556)), k1_zfmisc_1(u1_struct_0(B_556))) | ~m1_pre_topc(B_556, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1032])).
% 8.26/3.22  tff(c_12096, plain, (![D_557]: (v3_pre_topc(k9_subset_1(u1_struct_0('#skF_5'), D_557, k2_struct_0('#skF_5')), '#skF_5') | ~v3_pre_topc(D_557, '#skF_3') | ~m1_subset_1(D_557, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(k9_subset_1(k2_struct_0('#skF_5'), D_557, k2_struct_0('#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_12086])).
% 8.26/3.22  tff(c_12115, plain, (![D_558]: (v3_pre_topc(k3_xboole_0(D_558, k2_struct_0('#skF_5')), '#skF_5') | ~v3_pre_topc(D_558, '#skF_3') | ~m1_subset_1(D_558, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_163, c_150, c_101, c_150, c_101, c_12096])).
% 8.26/3.22  tff(c_12138, plain, (v3_pre_topc('#skF_4', '#skF_5') | ~v3_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_357, c_12115])).
% 8.26/3.22  tff(c_12148, plain, (v3_pre_topc('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_42, c_12138])).
% 8.26/3.22  tff(c_12150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_12148])).
% 8.26/3.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.26/3.22  
% 8.26/3.22  Inference rules
% 8.26/3.22  ----------------------
% 8.26/3.22  #Ref     : 0
% 8.26/3.22  #Sup     : 3079
% 8.26/3.22  #Fact    : 0
% 8.26/3.22  #Define  : 0
% 8.26/3.22  #Split   : 4
% 8.26/3.22  #Chain   : 0
% 8.26/3.22  #Close   : 0
% 8.26/3.22  
% 8.26/3.22  Ordering : KBO
% 8.26/3.22  
% 8.26/3.22  Simplification rules
% 8.26/3.22  ----------------------
% 8.26/3.22  #Subsume      : 744
% 8.26/3.22  #Demod        : 1926
% 8.26/3.22  #Tautology    : 1050
% 8.26/3.22  #SimpNegUnit  : 1
% 8.26/3.22  #BackRed      : 2
% 8.26/3.22  
% 8.26/3.22  #Partial instantiations: 0
% 8.26/3.22  #Strategies tried      : 1
% 8.26/3.22  
% 8.26/3.22  Timing (in seconds)
% 8.26/3.22  ----------------------
% 8.26/3.22  Preprocessing        : 0.34
% 8.26/3.22  Parsing              : 0.18
% 8.26/3.22  CNF conversion       : 0.03
% 8.26/3.22  Main loop            : 2.05
% 8.26/3.22  Inferencing          : 0.56
% 8.26/3.22  Reduction            : 0.86
% 8.26/3.22  Demodulation         : 0.68
% 8.26/3.22  BG Simplification    : 0.07
% 8.26/3.22  Subsumption          : 0.45
% 8.26/3.22  Abstraction          : 0.10
% 8.26/3.22  MUC search           : 0.00
% 8.26/3.22  Cooper               : 0.00
% 8.26/3.22  Total                : 2.42
% 8.26/3.22  Index Insertion      : 0.00
% 8.26/3.22  Index Deletion       : 0.00
% 8.26/3.22  Index Matching       : 0.00
% 8.26/3.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
