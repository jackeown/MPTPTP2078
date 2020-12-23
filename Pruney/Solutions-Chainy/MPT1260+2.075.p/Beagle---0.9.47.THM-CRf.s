%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:10 EST 2020

% Result     : Theorem 7.15s
% Output     : CNFRefutation 7.29s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 154 expanded)
%              Number of leaves         :   32 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  168 ( 376 expanded)
%              Number of equality atoms :   43 (  87 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_116,axiom,(
    ! [A] :
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

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_137,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_130,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_72,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_92,plain,(
    k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_66,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') != k2_tops_1('#skF_4','#skF_5')
    | ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_129,plain,(
    ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_66])).

tff(c_64,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_62,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_52,plain,(
    ! [C_52,A_40,D_54,B_48] :
      ( v3_pre_topc(C_52,A_40)
      | k1_tops_1(A_40,C_52) != C_52
      | ~ m1_subset_1(D_54,k1_zfmisc_1(u1_struct_0(B_48)))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(B_48)
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2019,plain,(
    ! [D_182,B_183] :
      ( ~ m1_subset_1(D_182,k1_zfmisc_1(u1_struct_0(B_183)))
      | ~ l1_pre_topc(B_183) ) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_2026,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_2019])).

tff(c_2031,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2026])).

tff(c_2069,plain,(
    ! [C_191,A_192] :
      ( v3_pre_topc(C_191,A_192)
      | k1_tops_1(A_192,C_191) != C_191
      | ~ m1_subset_1(C_191,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192) ) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2082,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | k1_tops_1('#skF_4','#skF_5') != '#skF_5'
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_2069])).

tff(c_2088,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | k1_tops_1('#skF_4','#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_2082])).

tff(c_2089,plain,(
    k1_tops_1('#skF_4','#skF_5') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_2088])).

tff(c_151,plain,(
    ! [A_94,B_95,C_96] :
      ( r2_hidden('#skF_1'(A_94,B_95,C_96),A_94)
      | r2_hidden('#skF_2'(A_94,B_95,C_96),C_96)
      | k4_xboole_0(A_94,B_95) = C_96 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_172,plain,(
    ! [A_94,B_95] :
      ( r2_hidden('#skF_2'(A_94,B_95,A_94),A_94)
      | k4_xboole_0(A_94,B_95) = A_94 ) ),
    inference(resolution,[status(thm)],[c_151,c_14])).

tff(c_1059,plain,(
    ! [A_153,B_154,C_155] :
      ( r2_hidden('#skF_1'(A_153,B_154,C_155),A_153)
      | r2_hidden('#skF_2'(A_153,B_154,C_155),B_154)
      | ~ r2_hidden('#skF_2'(A_153,B_154,C_155),A_153)
      | k4_xboole_0(A_153,B_154) = C_155 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5110,plain,(
    ! [A_262,B_263] :
      ( r2_hidden('#skF_2'(A_262,B_263,A_262),B_263)
      | ~ r2_hidden('#skF_2'(A_262,B_263,A_262),A_262)
      | k4_xboole_0(A_262,B_263) = A_262 ) ),
    inference(resolution,[status(thm)],[c_1059,c_8])).

tff(c_5126,plain,(
    ! [A_94,B_95] :
      ( r2_hidden('#skF_2'(A_94,B_95,A_94),B_95)
      | k4_xboole_0(A_94,B_95) = A_94 ) ),
    inference(resolution,[status(thm)],[c_172,c_5110])).

tff(c_138,plain,(
    ! [A_89,B_90] :
      ( m1_subset_1(k2_pre_topc(A_89,B_90),k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    ! [A_12,B_13,C_14] :
      ( k7_subset_1(A_12,B_13,C_14) = k4_xboole_0(B_13,C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5716,plain,(
    ! [A_284,B_285,C_286] :
      ( k7_subset_1(u1_struct_0(A_284),k2_pre_topc(A_284,B_285),C_286) = k4_xboole_0(k2_pre_topc(A_284,B_285),C_286)
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ l1_pre_topc(A_284) ) ),
    inference(resolution,[status(thm)],[c_138,c_28])).

tff(c_5728,plain,(
    ! [C_286] :
      ( k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),C_286) = k4_xboole_0(k2_pre_topc('#skF_4','#skF_5'),C_286)
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_5716])).

tff(c_5736,plain,(
    ! [C_287] : k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),C_287) = k4_xboole_0(k2_pre_topc('#skF_4','#skF_5'),C_287) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5728])).

tff(c_5746,plain,(
    k4_xboole_0(k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5736,c_92])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5785,plain,(
    ! [D_288] :
      ( ~ r2_hidden(D_288,'#skF_5')
      | ~ r2_hidden(D_288,k2_tops_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5746,c_4])).

tff(c_6116,plain,(
    ! [A_302] :
      ( ~ r2_hidden('#skF_2'(A_302,k2_tops_1('#skF_4','#skF_5'),A_302),'#skF_5')
      | k4_xboole_0(A_302,k2_tops_1('#skF_4','#skF_5')) = A_302 ) ),
    inference(resolution,[status(thm)],[c_5126,c_5785])).

tff(c_6129,plain,(
    k4_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_172,c_6116])).

tff(c_85,plain,(
    ! [A_78,B_79,C_80] :
      ( k7_subset_1(A_78,B_79,C_80) = k4_xboole_0(B_79,C_80)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_91,plain,(
    ! [C_80] : k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',C_80) = k4_xboole_0('#skF_5',C_80) ),
    inference(resolution,[status(thm)],[c_60,c_85])).

tff(c_208,plain,(
    ! [A_104,B_105] :
      ( k7_subset_1(u1_struct_0(A_104),B_105,k2_tops_1(A_104,B_105)) = k1_tops_1(A_104,B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_217,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_tops_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_208])).

tff(c_223,plain,(
    k4_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) = k1_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_91,c_217])).

tff(c_6130,plain,(
    k1_tops_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6129,c_223])).

tff(c_6132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2089,c_6130])).

tff(c_6134,plain,(
    k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') != k2_tops_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_6153,plain,(
    ! [A_307,B_308] :
      ( r1_tarski(k1_tops_1(A_307,B_308),B_308)
      | ~ m1_subset_1(B_308,k1_zfmisc_1(u1_struct_0(A_307)))
      | ~ l1_pre_topc(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6158,plain,
    ( r1_tarski(k1_tops_1('#skF_4','#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_6153])).

tff(c_6162,plain,(
    r1_tarski(k1_tops_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_6158])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6165,plain,
    ( k1_tops_1('#skF_4','#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_6162,c_20])).

tff(c_6166,plain,(
    ~ r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6165])).

tff(c_6133,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8003,plain,(
    ! [B_408,A_409,C_410] :
      ( r1_tarski(B_408,k1_tops_1(A_409,C_410))
      | ~ r1_tarski(B_408,C_410)
      | ~ v3_pre_topc(B_408,A_409)
      | ~ m1_subset_1(C_410,k1_zfmisc_1(u1_struct_0(A_409)))
      | ~ m1_subset_1(B_408,k1_zfmisc_1(u1_struct_0(A_409)))
      | ~ l1_pre_topc(A_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_8012,plain,(
    ! [B_408] :
      ( r1_tarski(B_408,k1_tops_1('#skF_4','#skF_5'))
      | ~ r1_tarski(B_408,'#skF_5')
      | ~ v3_pre_topc(B_408,'#skF_4')
      | ~ m1_subset_1(B_408,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_8003])).

tff(c_8019,plain,(
    ! [B_411] :
      ( r1_tarski(B_411,k1_tops_1('#skF_4','#skF_5'))
      | ~ r1_tarski(B_411,'#skF_5')
      | ~ v3_pre_topc(B_411,'#skF_4')
      | ~ m1_subset_1(B_411,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_8012])).

tff(c_8034,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_5','#skF_5')
    | ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_8019])).

tff(c_8044,plain,(
    r1_tarski('#skF_5',k1_tops_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6133,c_24,c_8034])).

tff(c_8046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6166,c_8044])).

tff(c_8047,plain,(
    k1_tops_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_6165])).

tff(c_8196,plain,(
    ! [A_436,B_437] :
      ( k7_subset_1(u1_struct_0(A_436),k2_pre_topc(A_436,B_437),k1_tops_1(A_436,B_437)) = k2_tops_1(A_436,B_437)
      | ~ m1_subset_1(B_437,k1_zfmisc_1(u1_struct_0(A_436)))
      | ~ l1_pre_topc(A_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8205,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8047,c_8196])).

tff(c_8209,plain,(
    k7_subset_1(u1_struct_0('#skF_4'),k2_pre_topc('#skF_4','#skF_5'),'#skF_5') = k2_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_8205])).

tff(c_8211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6134,c_8209])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:29:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.15/2.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.29/2.49  
% 7.29/2.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.29/2.49  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 7.29/2.49  
% 7.29/2.49  %Foreground sorts:
% 7.29/2.49  
% 7.29/2.49  
% 7.29/2.49  %Background operators:
% 7.29/2.49  
% 7.29/2.49  
% 7.29/2.49  %Foreground operators:
% 7.29/2.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.29/2.49  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.29/2.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.29/2.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.29/2.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.29/2.49  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 7.29/2.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.29/2.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.29/2.49  tff('#skF_5', type, '#skF_5': $i).
% 7.29/2.49  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.29/2.49  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 7.29/2.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.29/2.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.29/2.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.29/2.49  tff('#skF_4', type, '#skF_4': $i).
% 7.29/2.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.29/2.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.29/2.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 7.29/2.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.29/2.49  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.29/2.49  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.29/2.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.29/2.49  
% 7.29/2.51  tff(f_149, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 7.29/2.51  tff(f_116, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 7.29/2.51  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.29/2.51  tff(f_75, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 7.29/2.51  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 7.29/2.51  tff(f_137, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 7.29/2.51  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 7.29/2.51  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.29/2.51  tff(f_130, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 7.29/2.51  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 7.29/2.51  tff(c_72, plain, (v3_pre_topc('#skF_5', '#skF_4') | k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.29/2.51  tff(c_92, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_72])).
% 7.29/2.51  tff(c_66, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')!=k2_tops_1('#skF_4', '#skF_5') | ~v3_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.29/2.51  tff(c_129, plain, (~v3_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_66])).
% 7.29/2.51  tff(c_64, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.29/2.51  tff(c_62, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.29/2.51  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.29/2.51  tff(c_52, plain, (![C_52, A_40, D_54, B_48]: (v3_pre_topc(C_52, A_40) | k1_tops_1(A_40, C_52)!=C_52 | ~m1_subset_1(D_54, k1_zfmisc_1(u1_struct_0(B_48))) | ~m1_subset_1(C_52, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(B_48) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.29/2.51  tff(c_2019, plain, (![D_182, B_183]: (~m1_subset_1(D_182, k1_zfmisc_1(u1_struct_0(B_183))) | ~l1_pre_topc(B_183))), inference(splitLeft, [status(thm)], [c_52])).
% 7.29/2.51  tff(c_2026, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_2019])).
% 7.29/2.51  tff(c_2031, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_2026])).
% 7.29/2.51  tff(c_2069, plain, (![C_191, A_192]: (v3_pre_topc(C_191, A_192) | k1_tops_1(A_192, C_191)!=C_191 | ~m1_subset_1(C_191, k1_zfmisc_1(u1_struct_0(A_192))) | ~l1_pre_topc(A_192) | ~v2_pre_topc(A_192))), inference(splitRight, [status(thm)], [c_52])).
% 7.29/2.51  tff(c_2082, plain, (v3_pre_topc('#skF_5', '#skF_4') | k1_tops_1('#skF_4', '#skF_5')!='#skF_5' | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_2069])).
% 7.29/2.51  tff(c_2088, plain, (v3_pre_topc('#skF_5', '#skF_4') | k1_tops_1('#skF_4', '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_2082])).
% 7.29/2.51  tff(c_2089, plain, (k1_tops_1('#skF_4', '#skF_5')!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_129, c_2088])).
% 7.29/2.51  tff(c_151, plain, (![A_94, B_95, C_96]: (r2_hidden('#skF_1'(A_94, B_95, C_96), A_94) | r2_hidden('#skF_2'(A_94, B_95, C_96), C_96) | k4_xboole_0(A_94, B_95)=C_96)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.29/2.51  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.29/2.51  tff(c_172, plain, (![A_94, B_95]: (r2_hidden('#skF_2'(A_94, B_95, A_94), A_94) | k4_xboole_0(A_94, B_95)=A_94)), inference(resolution, [status(thm)], [c_151, c_14])).
% 7.29/2.51  tff(c_1059, plain, (![A_153, B_154, C_155]: (r2_hidden('#skF_1'(A_153, B_154, C_155), A_153) | r2_hidden('#skF_2'(A_153, B_154, C_155), B_154) | ~r2_hidden('#skF_2'(A_153, B_154, C_155), A_153) | k4_xboole_0(A_153, B_154)=C_155)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.29/2.51  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.29/2.51  tff(c_5110, plain, (![A_262, B_263]: (r2_hidden('#skF_2'(A_262, B_263, A_262), B_263) | ~r2_hidden('#skF_2'(A_262, B_263, A_262), A_262) | k4_xboole_0(A_262, B_263)=A_262)), inference(resolution, [status(thm)], [c_1059, c_8])).
% 7.29/2.51  tff(c_5126, plain, (![A_94, B_95]: (r2_hidden('#skF_2'(A_94, B_95, A_94), B_95) | k4_xboole_0(A_94, B_95)=A_94)), inference(resolution, [status(thm)], [c_172, c_5110])).
% 7.29/2.51  tff(c_138, plain, (![A_89, B_90]: (m1_subset_1(k2_pre_topc(A_89, B_90), k1_zfmisc_1(u1_struct_0(A_89))) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.29/2.51  tff(c_28, plain, (![A_12, B_13, C_14]: (k7_subset_1(A_12, B_13, C_14)=k4_xboole_0(B_13, C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.29/2.51  tff(c_5716, plain, (![A_284, B_285, C_286]: (k7_subset_1(u1_struct_0(A_284), k2_pre_topc(A_284, B_285), C_286)=k4_xboole_0(k2_pre_topc(A_284, B_285), C_286) | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0(A_284))) | ~l1_pre_topc(A_284))), inference(resolution, [status(thm)], [c_138, c_28])).
% 7.29/2.51  tff(c_5728, plain, (![C_286]: (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), C_286)=k4_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), C_286) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_5716])).
% 7.29/2.51  tff(c_5736, plain, (![C_287]: (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), C_287)=k4_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), C_287))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5728])).
% 7.29/2.51  tff(c_5746, plain, (k4_xboole_0(k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5736, c_92])).
% 7.29/2.51  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.29/2.51  tff(c_5785, plain, (![D_288]: (~r2_hidden(D_288, '#skF_5') | ~r2_hidden(D_288, k2_tops_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_5746, c_4])).
% 7.29/2.51  tff(c_6116, plain, (![A_302]: (~r2_hidden('#skF_2'(A_302, k2_tops_1('#skF_4', '#skF_5'), A_302), '#skF_5') | k4_xboole_0(A_302, k2_tops_1('#skF_4', '#skF_5'))=A_302)), inference(resolution, [status(thm)], [c_5126, c_5785])).
% 7.29/2.51  tff(c_6129, plain, (k4_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_172, c_6116])).
% 7.29/2.51  tff(c_85, plain, (![A_78, B_79, C_80]: (k7_subset_1(A_78, B_79, C_80)=k4_xboole_0(B_79, C_80) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.29/2.51  tff(c_91, plain, (![C_80]: (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', C_80)=k4_xboole_0('#skF_5', C_80))), inference(resolution, [status(thm)], [c_60, c_85])).
% 7.29/2.51  tff(c_208, plain, (![A_104, B_105]: (k7_subset_1(u1_struct_0(A_104), B_105, k2_tops_1(A_104, B_105))=k1_tops_1(A_104, B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.29/2.51  tff(c_217, plain, (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_tops_1('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_208])).
% 7.29/2.51  tff(c_223, plain, (k4_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k1_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_91, c_217])).
% 7.29/2.51  tff(c_6130, plain, (k1_tops_1('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6129, c_223])).
% 7.29/2.51  tff(c_6132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2089, c_6130])).
% 7.29/2.51  tff(c_6134, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')!=k2_tops_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_72])).
% 7.29/2.51  tff(c_6153, plain, (![A_307, B_308]: (r1_tarski(k1_tops_1(A_307, B_308), B_308) | ~m1_subset_1(B_308, k1_zfmisc_1(u1_struct_0(A_307))) | ~l1_pre_topc(A_307))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.29/2.51  tff(c_6158, plain, (r1_tarski(k1_tops_1('#skF_4', '#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_6153])).
% 7.29/2.51  tff(c_6162, plain, (r1_tarski(k1_tops_1('#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_6158])).
% 7.29/2.51  tff(c_20, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.29/2.51  tff(c_6165, plain, (k1_tops_1('#skF_4', '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_6162, c_20])).
% 7.29/2.51  tff(c_6166, plain, (~r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_6165])).
% 7.29/2.51  tff(c_6133, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_72])).
% 7.29/2.51  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.29/2.51  tff(c_8003, plain, (![B_408, A_409, C_410]: (r1_tarski(B_408, k1_tops_1(A_409, C_410)) | ~r1_tarski(B_408, C_410) | ~v3_pre_topc(B_408, A_409) | ~m1_subset_1(C_410, k1_zfmisc_1(u1_struct_0(A_409))) | ~m1_subset_1(B_408, k1_zfmisc_1(u1_struct_0(A_409))) | ~l1_pre_topc(A_409))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.29/2.51  tff(c_8012, plain, (![B_408]: (r1_tarski(B_408, k1_tops_1('#skF_4', '#skF_5')) | ~r1_tarski(B_408, '#skF_5') | ~v3_pre_topc(B_408, '#skF_4') | ~m1_subset_1(B_408, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_8003])).
% 7.29/2.51  tff(c_8019, plain, (![B_411]: (r1_tarski(B_411, k1_tops_1('#skF_4', '#skF_5')) | ~r1_tarski(B_411, '#skF_5') | ~v3_pre_topc(B_411, '#skF_4') | ~m1_subset_1(B_411, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_8012])).
% 7.29/2.51  tff(c_8034, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5')) | ~r1_tarski('#skF_5', '#skF_5') | ~v3_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_8019])).
% 7.29/2.51  tff(c_8044, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6133, c_24, c_8034])).
% 7.29/2.51  tff(c_8046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6166, c_8044])).
% 7.29/2.51  tff(c_8047, plain, (k1_tops_1('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_6165])).
% 7.29/2.51  tff(c_8196, plain, (![A_436, B_437]: (k7_subset_1(u1_struct_0(A_436), k2_pre_topc(A_436, B_437), k1_tops_1(A_436, B_437))=k2_tops_1(A_436, B_437) | ~m1_subset_1(B_437, k1_zfmisc_1(u1_struct_0(A_436))) | ~l1_pre_topc(A_436))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.29/2.51  tff(c_8205, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8047, c_8196])).
% 7.29/2.51  tff(c_8209, plain, (k7_subset_1(u1_struct_0('#skF_4'), k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')=k2_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_8205])).
% 7.29/2.51  tff(c_8211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6134, c_8209])).
% 7.29/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.29/2.51  
% 7.29/2.51  Inference rules
% 7.29/2.51  ----------------------
% 7.29/2.51  #Ref     : 0
% 7.29/2.51  #Sup     : 2568
% 7.29/2.51  #Fact    : 2
% 7.29/2.51  #Define  : 0
% 7.29/2.51  #Split   : 6
% 7.29/2.51  #Chain   : 0
% 7.29/2.51  #Close   : 0
% 7.29/2.51  
% 7.29/2.51  Ordering : KBO
% 7.29/2.51  
% 7.29/2.51  Simplification rules
% 7.29/2.51  ----------------------
% 7.29/2.51  #Subsume      : 1489
% 7.29/2.51  #Demod        : 481
% 7.29/2.51  #Tautology    : 175
% 7.29/2.51  #SimpNegUnit  : 6
% 7.29/2.51  #BackRed      : 14
% 7.29/2.51  
% 7.29/2.51  #Partial instantiations: 0
% 7.29/2.51  #Strategies tried      : 1
% 7.29/2.51  
% 7.29/2.51  Timing (in seconds)
% 7.29/2.51  ----------------------
% 7.29/2.51  Preprocessing        : 0.36
% 7.29/2.51  Parsing              : 0.20
% 7.29/2.51  CNF conversion       : 0.03
% 7.29/2.51  Main loop            : 1.34
% 7.29/2.51  Inferencing          : 0.43
% 7.29/2.51  Reduction            : 0.52
% 7.29/2.51  Demodulation         : 0.43
% 7.29/2.51  BG Simplification    : 0.05
% 7.29/2.51  Subsumption          : 0.25
% 7.29/2.51  Abstraction          : 0.08
% 7.29/2.51  MUC search           : 0.00
% 7.29/2.51  Cooper               : 0.00
% 7.29/2.51  Total                : 1.74
% 7.29/2.51  Index Insertion      : 0.00
% 7.29/2.51  Index Deletion       : 0.00
% 7.29/2.51  Index Matching       : 0.00
% 7.29/2.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
