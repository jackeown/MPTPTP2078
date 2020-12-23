%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:00 EST 2020

% Result     : Theorem 13.70s
% Output     : CNFRefutation 13.70s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 188 expanded)
%              Number of leaves         :   34 (  82 expanded)
%              Depth                    :   10
%              Number of atoms          :  104 ( 429 expanded)
%              Number of equality atoms :   18 (  77 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_118,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_100,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_2)).

tff(c_62,plain,(
    ~ v3_pre_topc('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_74,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_70,plain,(
    m1_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_171,plain,(
    ! [B_103,A_104] :
      ( l1_pre_topc(B_103)
      | ~ m1_pre_topc(B_103,A_104)
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_174,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_171])).

tff(c_177,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_174])).

tff(c_50,plain,(
    ! [A_55] :
      ( l1_struct_0(A_55)
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_117,plain,(
    ! [A_96] :
      ( u1_struct_0(A_96) = k2_struct_0(A_96)
      | ~ l1_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_121,plain,(
    ! [A_55] :
      ( u1_struct_0(A_55) = k2_struct_0(A_55)
      | ~ l1_pre_topc(A_55) ) ),
    inference(resolution,[status(thm)],[c_50,c_117])).

tff(c_181,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_177,c_121])).

tff(c_66,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_184,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_66])).

tff(c_122,plain,(
    ! [A_97] :
      ( u1_struct_0(A_97) = k2_struct_0(A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_50,c_117])).

tff(c_126,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_122])).

tff(c_64,plain,(
    '#skF_6' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_72,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_76,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_72])).

tff(c_127,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_76])).

tff(c_68,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_75,plain,(
    v3_pre_topc('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68])).

tff(c_137,plain,(
    ! [A_100,B_101] :
      ( r1_tarski(A_100,B_101)
      | ~ m1_subset_1(A_100,k1_zfmisc_1(B_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_145,plain,(
    r1_tarski('#skF_8',u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_66,c_137])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_158,plain,(
    k3_xboole_0('#skF_8',u1_struct_0('#skF_7')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_145,c_10])).

tff(c_182,plain,(
    k3_xboole_0('#skF_8',k2_struct_0('#skF_7')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_158])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_238,plain,(
    ! [A_111,B_112,C_113] :
      ( k9_subset_1(A_111,B_112,C_113) = k3_xboole_0(B_112,C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(A_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_323,plain,(
    ! [B_119,B_120,A_121] :
      ( k9_subset_1(B_119,B_120,A_121) = k3_xboole_0(B_120,A_121)
      | ~ r1_tarski(A_121,B_119) ) ),
    inference(resolution,[status(thm)],[c_18,c_238])).

tff(c_334,plain,(
    ! [B_4,B_120] : k9_subset_1(B_4,B_120,B_4) = k3_xboole_0(B_120,B_4) ),
    inference(resolution,[status(thm)],[c_8,c_323])).

tff(c_2427,plain,(
    ! [B_226,D_227,A_228] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_226),D_227,k2_struct_0(B_226)),B_226)
      | ~ v3_pre_topc(D_227,A_228)
      | ~ m1_subset_1(D_227,k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_226),D_227,k2_struct_0(B_226)),k1_zfmisc_1(u1_struct_0(B_226)))
      | ~ m1_pre_topc(B_226,A_228)
      | ~ l1_pre_topc(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2442,plain,(
    ! [B_226,D_227] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_226),D_227,k2_struct_0(B_226)),B_226)
      | ~ v3_pre_topc(D_227,'#skF_5')
      | ~ m1_subset_1(D_227,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_226),D_227,k2_struct_0(B_226)),k1_zfmisc_1(u1_struct_0(B_226)))
      | ~ m1_pre_topc(B_226,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_2427])).

tff(c_3165,plain,(
    ! [B_240,D_241] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_240),D_241,k2_struct_0(B_240)),B_240)
      | ~ v3_pre_topc(D_241,'#skF_5')
      | ~ m1_subset_1(D_241,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_240),D_241,k2_struct_0(B_240)),k1_zfmisc_1(u1_struct_0(B_240)))
      | ~ m1_pre_topc(B_240,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2442])).

tff(c_3183,plain,(
    ! [D_241] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0('#skF_7'),D_241,k2_struct_0('#skF_7')),'#skF_7')
      | ~ v3_pre_topc(D_241,'#skF_5')
      | ~ m1_subset_1(D_241,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_7'),D_241,k2_struct_0('#skF_7')),k1_zfmisc_1(k2_struct_0('#skF_7')))
      | ~ m1_pre_topc('#skF_7','#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_3165])).

tff(c_13333,plain,(
    ! [D_431] :
      ( v3_pre_topc(k3_xboole_0(D_431,k2_struct_0('#skF_7')),'#skF_7')
      | ~ v3_pre_topc(D_431,'#skF_5')
      | ~ m1_subset_1(D_431,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(k3_xboole_0(D_431,k2_struct_0('#skF_7')),k1_zfmisc_1(k2_struct_0('#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_334,c_181,c_334,c_181,c_3183])).

tff(c_13350,plain,
    ( v3_pre_topc(k3_xboole_0('#skF_8',k2_struct_0('#skF_7')),'#skF_7')
    | ~ v3_pre_topc('#skF_8','#skF_5')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_13333])).

tff(c_13371,plain,(
    v3_pre_topc('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_127,c_75,c_182,c_13350])).

tff(c_13373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_13371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:12:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.70/5.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.70/5.48  
% 13.70/5.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.70/5.48  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2
% 13.70/5.48  
% 13.70/5.48  %Foreground sorts:
% 13.70/5.48  
% 13.70/5.48  
% 13.70/5.48  %Background operators:
% 13.70/5.48  
% 13.70/5.48  
% 13.70/5.48  %Foreground operators:
% 13.70/5.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 13.70/5.48  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 13.70/5.48  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 13.70/5.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.70/5.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.70/5.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.70/5.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 13.70/5.48  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 13.70/5.48  tff('#skF_7', type, '#skF_7': $i).
% 13.70/5.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 13.70/5.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.70/5.48  tff('#skF_5', type, '#skF_5': $i).
% 13.70/5.48  tff('#skF_6', type, '#skF_6': $i).
% 13.70/5.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.70/5.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 13.70/5.48  tff('#skF_8', type, '#skF_8': $i).
% 13.70/5.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.70/5.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.70/5.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.70/5.48  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 13.70/5.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.70/5.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.70/5.48  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 13.70/5.48  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 13.70/5.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.70/5.48  
% 13.70/5.49  tff(f_118, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 13.70/5.49  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 13.70/5.49  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 13.70/5.49  tff(f_51, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 13.70/5.49  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 13.70/5.49  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.70/5.49  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.70/5.49  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 13.70/5.49  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (v3_pre_topc(C, B) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & (k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)) = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tops_2)).
% 13.70/5.49  tff(c_62, plain, (~v3_pre_topc('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_118])).
% 13.70/5.49  tff(c_74, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 13.70/5.49  tff(c_70, plain, (m1_pre_topc('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 13.70/5.49  tff(c_171, plain, (![B_103, A_104]: (l1_pre_topc(B_103) | ~m1_pre_topc(B_103, A_104) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_83])).
% 13.70/5.49  tff(c_174, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_70, c_171])).
% 13.70/5.49  tff(c_177, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_174])).
% 13.70/5.49  tff(c_50, plain, (![A_55]: (l1_struct_0(A_55) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.70/5.49  tff(c_117, plain, (![A_96]: (u1_struct_0(A_96)=k2_struct_0(A_96) | ~l1_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.70/5.49  tff(c_121, plain, (![A_55]: (u1_struct_0(A_55)=k2_struct_0(A_55) | ~l1_pre_topc(A_55))), inference(resolution, [status(thm)], [c_50, c_117])).
% 13.70/5.49  tff(c_181, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_177, c_121])).
% 13.70/5.49  tff(c_66, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 13.70/5.49  tff(c_184, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_66])).
% 13.70/5.49  tff(c_122, plain, (![A_97]: (u1_struct_0(A_97)=k2_struct_0(A_97) | ~l1_pre_topc(A_97))), inference(resolution, [status(thm)], [c_50, c_117])).
% 13.70/5.49  tff(c_126, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_74, c_122])).
% 13.70/5.49  tff(c_64, plain, ('#skF_6'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_118])).
% 13.70/5.49  tff(c_72, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 13.70/5.49  tff(c_76, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_72])).
% 13.70/5.49  tff(c_127, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_76])).
% 13.70/5.49  tff(c_68, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 13.70/5.49  tff(c_75, plain, (v3_pre_topc('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68])).
% 13.70/5.49  tff(c_137, plain, (![A_100, B_101]: (r1_tarski(A_100, B_101) | ~m1_subset_1(A_100, k1_zfmisc_1(B_101)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.70/5.49  tff(c_145, plain, (r1_tarski('#skF_8', u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_137])).
% 13.70/5.49  tff(c_10, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.70/5.49  tff(c_158, plain, (k3_xboole_0('#skF_8', u1_struct_0('#skF_7'))='#skF_8'), inference(resolution, [status(thm)], [c_145, c_10])).
% 13.70/5.49  tff(c_182, plain, (k3_xboole_0('#skF_8', k2_struct_0('#skF_7'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_181, c_158])).
% 13.70/5.49  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.70/5.49  tff(c_18, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.70/5.49  tff(c_238, plain, (![A_111, B_112, C_113]: (k9_subset_1(A_111, B_112, C_113)=k3_xboole_0(B_112, C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(A_111)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.70/5.49  tff(c_323, plain, (![B_119, B_120, A_121]: (k9_subset_1(B_119, B_120, A_121)=k3_xboole_0(B_120, A_121) | ~r1_tarski(A_121, B_119))), inference(resolution, [status(thm)], [c_18, c_238])).
% 13.70/5.49  tff(c_334, plain, (![B_4, B_120]: (k9_subset_1(B_4, B_120, B_4)=k3_xboole_0(B_120, B_4))), inference(resolution, [status(thm)], [c_8, c_323])).
% 13.70/5.49  tff(c_2427, plain, (![B_226, D_227, A_228]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_226), D_227, k2_struct_0(B_226)), B_226) | ~v3_pre_topc(D_227, A_228) | ~m1_subset_1(D_227, k1_zfmisc_1(u1_struct_0(A_228))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_226), D_227, k2_struct_0(B_226)), k1_zfmisc_1(u1_struct_0(B_226))) | ~m1_pre_topc(B_226, A_228) | ~l1_pre_topc(A_228))), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.70/5.49  tff(c_2442, plain, (![B_226, D_227]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_226), D_227, k2_struct_0(B_226)), B_226) | ~v3_pre_topc(D_227, '#skF_5') | ~m1_subset_1(D_227, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_226), D_227, k2_struct_0(B_226)), k1_zfmisc_1(u1_struct_0(B_226))) | ~m1_pre_topc(B_226, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_2427])).
% 13.70/5.49  tff(c_3165, plain, (![B_240, D_241]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_240), D_241, k2_struct_0(B_240)), B_240) | ~v3_pre_topc(D_241, '#skF_5') | ~m1_subset_1(D_241, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_240), D_241, k2_struct_0(B_240)), k1_zfmisc_1(u1_struct_0(B_240))) | ~m1_pre_topc(B_240, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2442])).
% 13.70/5.49  tff(c_3183, plain, (![D_241]: (v3_pre_topc(k9_subset_1(u1_struct_0('#skF_7'), D_241, k2_struct_0('#skF_7')), '#skF_7') | ~v3_pre_topc(D_241, '#skF_5') | ~m1_subset_1(D_241, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(k9_subset_1(u1_struct_0('#skF_7'), D_241, k2_struct_0('#skF_7')), k1_zfmisc_1(k2_struct_0('#skF_7'))) | ~m1_pre_topc('#skF_7', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_181, c_3165])).
% 13.70/5.49  tff(c_13333, plain, (![D_431]: (v3_pre_topc(k3_xboole_0(D_431, k2_struct_0('#skF_7')), '#skF_7') | ~v3_pre_topc(D_431, '#skF_5') | ~m1_subset_1(D_431, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(k3_xboole_0(D_431, k2_struct_0('#skF_7')), k1_zfmisc_1(k2_struct_0('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_334, c_181, c_334, c_181, c_3183])).
% 13.70/5.49  tff(c_13350, plain, (v3_pre_topc(k3_xboole_0('#skF_8', k2_struct_0('#skF_7')), '#skF_7') | ~v3_pre_topc('#skF_8', '#skF_5') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_struct_0('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_182, c_13333])).
% 13.70/5.49  tff(c_13371, plain, (v3_pre_topc('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_184, c_127, c_75, c_182, c_13350])).
% 13.70/5.49  tff(c_13373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_13371])).
% 13.70/5.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.70/5.49  
% 13.70/5.49  Inference rules
% 13.70/5.49  ----------------------
% 13.70/5.49  #Ref     : 0
% 13.70/5.49  #Sup     : 3482
% 13.70/5.49  #Fact    : 0
% 13.70/5.49  #Define  : 0
% 13.70/5.49  #Split   : 7
% 13.70/5.49  #Chain   : 0
% 13.70/5.49  #Close   : 0
% 13.70/5.49  
% 13.70/5.49  Ordering : KBO
% 13.70/5.49  
% 13.70/5.49  Simplification rules
% 13.70/5.49  ----------------------
% 13.70/5.49  #Subsume      : 243
% 13.70/5.49  #Demod        : 5938
% 13.70/5.49  #Tautology    : 906
% 13.70/5.49  #SimpNegUnit  : 6
% 13.70/5.49  #BackRed      : 4
% 13.70/5.49  
% 13.70/5.49  #Partial instantiations: 0
% 13.70/5.49  #Strategies tried      : 1
% 13.70/5.49  
% 13.70/5.49  Timing (in seconds)
% 13.70/5.49  ----------------------
% 13.70/5.50  Preprocessing        : 0.34
% 13.70/5.50  Parsing              : 0.17
% 13.70/5.50  CNF conversion       : 0.03
% 13.70/5.50  Main loop            : 4.38
% 13.70/5.50  Inferencing          : 0.82
% 13.70/5.50  Reduction            : 2.72
% 13.70/5.50  Demodulation         : 2.48
% 13.70/5.50  BG Simplification    : 0.12
% 13.70/5.50  Subsumption          : 0.58
% 13.70/5.50  Abstraction          : 0.24
% 13.70/5.50  MUC search           : 0.00
% 13.70/5.50  Cooper               : 0.00
% 13.70/5.50  Total                : 4.74
% 13.70/5.50  Index Insertion      : 0.00
% 13.70/5.50  Index Deletion       : 0.00
% 13.70/5.50  Index Matching       : 0.00
% 13.70/5.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
