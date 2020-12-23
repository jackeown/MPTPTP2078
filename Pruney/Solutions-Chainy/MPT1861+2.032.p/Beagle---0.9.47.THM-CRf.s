%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:13 EST 2020

% Result     : Theorem 17.48s
% Output     : CNFRefutation 17.61s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 131 expanded)
%              Number of leaves         :   25 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  118 ( 280 expanded)
%              Number of equality atoms :   12 (  30 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

tff(f_49,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8037,plain,(
    ! [A_783,B_784,C_785] :
      ( k9_subset_1(A_783,B_784,C_785) = k3_xboole_0(B_784,C_785)
      | ~ m1_subset_1(C_785,k1_zfmisc_1(A_783)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8051,plain,(
    ! [B_784] : k9_subset_1(u1_struct_0('#skF_2'),B_784,'#skF_4') = k3_xboole_0(B_784,'#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_8037])).

tff(c_26,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8067,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8051,c_26])).

tff(c_28,plain,
    ( v2_tex_2('#skF_4','#skF_2')
    | v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_38,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8068,plain,(
    ! [B_788] : k9_subset_1(u1_struct_0('#skF_2'),B_788,'#skF_4') = k3_xboole_0(B_788,'#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_8037])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k9_subset_1(A_8,B_9,C_10),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8074,plain,(
    ! [B_788] :
      ( m1_subset_1(k3_xboole_0(B_788,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8068,c_8])).

tff(c_8080,plain,(
    ! [B_788] : m1_subset_1(k3_xboole_0(B_788,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_8074])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8114,plain,(
    ! [C_795,A_796,B_797] :
      ( v2_tex_2(C_795,A_796)
      | ~ v2_tex_2(B_797,A_796)
      | ~ r1_tarski(C_795,B_797)
      | ~ m1_subset_1(C_795,k1_zfmisc_1(u1_struct_0(A_796)))
      | ~ m1_subset_1(B_797,k1_zfmisc_1(u1_struct_0(A_796)))
      | ~ l1_pre_topc(A_796) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_9824,plain,(
    ! [A_955,B_956,A_957] :
      ( v2_tex_2(k3_xboole_0(A_955,B_956),A_957)
      | ~ v2_tex_2(A_955,A_957)
      | ~ m1_subset_1(k3_xboole_0(A_955,B_956),k1_zfmisc_1(u1_struct_0(A_957)))
      | ~ m1_subset_1(A_955,k1_zfmisc_1(u1_struct_0(A_957)))
      | ~ l1_pre_topc(A_957) ) ),
    inference(resolution,[status(thm)],[c_2,c_8114])).

tff(c_9837,plain,(
    ! [B_788] :
      ( v2_tex_2(k3_xboole_0(B_788,'#skF_4'),'#skF_2')
      | ~ v2_tex_2(B_788,'#skF_2')
      | ~ m1_subset_1(B_788,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8080,c_9824])).

tff(c_14438,plain,(
    ! [B_1201] :
      ( v2_tex_2(k3_xboole_0(B_1201,'#skF_4'),'#skF_2')
      | ~ v2_tex_2(B_1201,'#skF_2')
      | ~ m1_subset_1(B_1201,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_9837])).

tff(c_14482,plain,
    ( v2_tex_2(k3_xboole_0('#skF_3','#skF_4'),'#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_14438])).

tff(c_14497,plain,(
    v2_tex_2(k3_xboole_0('#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_14482])).

tff(c_14499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8067,c_14497])).

tff(c_14500,plain,(
    v2_tex_2('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_31066,plain,(
    ! [A_2197,B_2198,C_2199] :
      ( k9_subset_1(A_2197,B_2198,C_2199) = k3_xboole_0(B_2198,C_2199)
      | ~ m1_subset_1(C_2199,k1_zfmisc_1(A_2197)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_31118,plain,(
    ! [B_2207] : k9_subset_1(u1_struct_0('#skF_2'),B_2207,'#skF_4') = k3_xboole_0(B_2207,'#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_31066])).

tff(c_31124,plain,(
    ! [B_2207] :
      ( m1_subset_1(k3_xboole_0(B_2207,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31118,c_8])).

tff(c_31130,plain,(
    ! [B_2207] : m1_subset_1(k3_xboole_0(B_2207,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_31124])).

tff(c_12,plain,(
    ! [A_14] : ~ v1_subset_1('#skF_1'(A_14),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_14] : m1_subset_1('#skF_1'(A_14),k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14611,plain,(
    ! [B_1224,A_1225] :
      ( v1_subset_1(B_1224,A_1225)
      | B_1224 = A_1225
      | ~ m1_subset_1(B_1224,k1_zfmisc_1(A_1225)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14620,plain,(
    ! [A_14] :
      ( v1_subset_1('#skF_1'(A_14),A_14)
      | '#skF_1'(A_14) = A_14 ) ),
    inference(resolution,[status(thm)],[c_14,c_14611])).

tff(c_14628,plain,(
    ! [A_14] : '#skF_1'(A_14) = A_14 ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_14620])).

tff(c_14636,plain,(
    ! [A_14] : m1_subset_1(A_14,k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14628,c_14])).

tff(c_31078,plain,(
    ! [A_14,B_2198] : k9_subset_1(A_14,B_2198,A_14) = k3_xboole_0(B_2198,A_14) ),
    inference(resolution,[status(thm)],[c_14636,c_31066])).

tff(c_15232,plain,(
    ! [A_1295,B_1296,C_1297] :
      ( m1_subset_1(k9_subset_1(A_1295,B_1296,C_1297),k1_zfmisc_1(A_1295))
      | ~ m1_subset_1(C_1297,k1_zfmisc_1(A_1295)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_31297,plain,(
    ! [A_2230,B_2231,C_2232] :
      ( r1_tarski(k9_subset_1(A_2230,B_2231,C_2232),A_2230)
      | ~ m1_subset_1(C_2232,k1_zfmisc_1(A_2230)) ) ),
    inference(resolution,[status(thm)],[c_15232,c_16])).

tff(c_24,plain,(
    ! [C_26,A_20,B_24] :
      ( v2_tex_2(C_26,A_20)
      | ~ v2_tex_2(B_24,A_20)
      | ~ r1_tarski(C_26,B_24)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36164,plain,(
    ! [A_2546,B_2547,C_2548,A_2549] :
      ( v2_tex_2(k9_subset_1(A_2546,B_2547,C_2548),A_2549)
      | ~ v2_tex_2(A_2546,A_2549)
      | ~ m1_subset_1(k9_subset_1(A_2546,B_2547,C_2548),k1_zfmisc_1(u1_struct_0(A_2549)))
      | ~ m1_subset_1(A_2546,k1_zfmisc_1(u1_struct_0(A_2549)))
      | ~ l1_pre_topc(A_2549)
      | ~ m1_subset_1(C_2548,k1_zfmisc_1(A_2546)) ) ),
    inference(resolution,[status(thm)],[c_31297,c_24])).

tff(c_36200,plain,(
    ! [A_14,B_2198,A_2549] :
      ( v2_tex_2(k9_subset_1(A_14,B_2198,A_14),A_2549)
      | ~ v2_tex_2(A_14,A_2549)
      | ~ m1_subset_1(k3_xboole_0(B_2198,A_14),k1_zfmisc_1(u1_struct_0(A_2549)))
      | ~ m1_subset_1(A_14,k1_zfmisc_1(u1_struct_0(A_2549)))
      | ~ l1_pre_topc(A_2549)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31078,c_36164])).

tff(c_55333,plain,(
    ! [B_3309,A_3310,A_3311] :
      ( v2_tex_2(k3_xboole_0(B_3309,A_3310),A_3311)
      | ~ v2_tex_2(A_3310,A_3311)
      | ~ m1_subset_1(k3_xboole_0(B_3309,A_3310),k1_zfmisc_1(u1_struct_0(A_3311)))
      | ~ m1_subset_1(A_3310,k1_zfmisc_1(u1_struct_0(A_3311)))
      | ~ l1_pre_topc(A_3311) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14636,c_31078,c_36200])).

tff(c_55387,plain,(
    ! [B_2207] :
      ( v2_tex_2(k3_xboole_0(B_2207,'#skF_4'),'#skF_2')
      | ~ v2_tex_2('#skF_4','#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_31130,c_55333])).

tff(c_55438,plain,(
    ! [B_2207] : v2_tex_2(k3_xboole_0(B_2207,'#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_14500,c_55387])).

tff(c_31080,plain,(
    ! [B_2198] : k9_subset_1(u1_struct_0('#skF_2'),B_2198,'#skF_4') = k3_xboole_0(B_2198,'#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_31066])).

tff(c_31117,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31080,c_26])).

tff(c_55450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55438,c_31117])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:30:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.48/10.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.48/10.19  
% 17.48/10.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.48/10.19  %$ v2_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 17.48/10.19  
% 17.48/10.19  %Foreground sorts:
% 17.48/10.19  
% 17.48/10.19  
% 17.48/10.19  %Background operators:
% 17.48/10.19  
% 17.48/10.19  
% 17.48/10.19  %Foreground operators:
% 17.48/10.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.48/10.19  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 17.48/10.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.48/10.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 17.48/10.19  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 17.48/10.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.48/10.19  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 17.48/10.19  tff('#skF_2', type, '#skF_2': $i).
% 17.48/10.19  tff('#skF_3', type, '#skF_3': $i).
% 17.48/10.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.48/10.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.48/10.19  tff('#skF_4', type, '#skF_4': $i).
% 17.48/10.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.48/10.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.48/10.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 17.48/10.19  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 17.48/10.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.48/10.19  
% 17.61/10.21  tff(f_89, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 17.61/10.21  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 17.61/10.21  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 17.61/10.21  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 17.61/10.21  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 17.61/10.21  tff(f_49, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 17.61/10.21  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 17.61/10.21  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 17.61/10.21  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 17.61/10.21  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 17.61/10.21  tff(c_8037, plain, (![A_783, B_784, C_785]: (k9_subset_1(A_783, B_784, C_785)=k3_xboole_0(B_784, C_785) | ~m1_subset_1(C_785, k1_zfmisc_1(A_783)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.61/10.21  tff(c_8051, plain, (![B_784]: (k9_subset_1(u1_struct_0('#skF_2'), B_784, '#skF_4')=k3_xboole_0(B_784, '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_8037])).
% 17.61/10.21  tff(c_26, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 17.61/10.21  tff(c_8067, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8051, c_26])).
% 17.61/10.21  tff(c_28, plain, (v2_tex_2('#skF_4', '#skF_2') | v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 17.61/10.21  tff(c_38, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_28])).
% 17.61/10.21  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 17.61/10.21  tff(c_8068, plain, (![B_788]: (k9_subset_1(u1_struct_0('#skF_2'), B_788, '#skF_4')=k3_xboole_0(B_788, '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_8037])).
% 17.61/10.21  tff(c_8, plain, (![A_8, B_9, C_10]: (m1_subset_1(k9_subset_1(A_8, B_9, C_10), k1_zfmisc_1(A_8)) | ~m1_subset_1(C_10, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 17.61/10.21  tff(c_8074, plain, (![B_788]: (m1_subset_1(k3_xboole_0(B_788, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_8068, c_8])).
% 17.61/10.21  tff(c_8080, plain, (![B_788]: (m1_subset_1(k3_xboole_0(B_788, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_8074])).
% 17.61/10.21  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 17.61/10.21  tff(c_8114, plain, (![C_795, A_796, B_797]: (v2_tex_2(C_795, A_796) | ~v2_tex_2(B_797, A_796) | ~r1_tarski(C_795, B_797) | ~m1_subset_1(C_795, k1_zfmisc_1(u1_struct_0(A_796))) | ~m1_subset_1(B_797, k1_zfmisc_1(u1_struct_0(A_796))) | ~l1_pre_topc(A_796))), inference(cnfTransformation, [status(thm)], [f_74])).
% 17.61/10.21  tff(c_9824, plain, (![A_955, B_956, A_957]: (v2_tex_2(k3_xboole_0(A_955, B_956), A_957) | ~v2_tex_2(A_955, A_957) | ~m1_subset_1(k3_xboole_0(A_955, B_956), k1_zfmisc_1(u1_struct_0(A_957))) | ~m1_subset_1(A_955, k1_zfmisc_1(u1_struct_0(A_957))) | ~l1_pre_topc(A_957))), inference(resolution, [status(thm)], [c_2, c_8114])).
% 17.61/10.21  tff(c_9837, plain, (![B_788]: (v2_tex_2(k3_xboole_0(B_788, '#skF_4'), '#skF_2') | ~v2_tex_2(B_788, '#skF_2') | ~m1_subset_1(B_788, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_8080, c_9824])).
% 17.61/10.21  tff(c_14438, plain, (![B_1201]: (v2_tex_2(k3_xboole_0(B_1201, '#skF_4'), '#skF_2') | ~v2_tex_2(B_1201, '#skF_2') | ~m1_subset_1(B_1201, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_9837])).
% 17.61/10.21  tff(c_14482, plain, (v2_tex_2(k3_xboole_0('#skF_3', '#skF_4'), '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_14438])).
% 17.61/10.21  tff(c_14497, plain, (v2_tex_2(k3_xboole_0('#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_14482])).
% 17.61/10.21  tff(c_14499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8067, c_14497])).
% 17.61/10.21  tff(c_14500, plain, (v2_tex_2('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_28])).
% 17.61/10.21  tff(c_31066, plain, (![A_2197, B_2198, C_2199]: (k9_subset_1(A_2197, B_2198, C_2199)=k3_xboole_0(B_2198, C_2199) | ~m1_subset_1(C_2199, k1_zfmisc_1(A_2197)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.61/10.21  tff(c_31118, plain, (![B_2207]: (k9_subset_1(u1_struct_0('#skF_2'), B_2207, '#skF_4')=k3_xboole_0(B_2207, '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_31066])).
% 17.61/10.21  tff(c_31124, plain, (![B_2207]: (m1_subset_1(k3_xboole_0(B_2207, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_31118, c_8])).
% 17.61/10.21  tff(c_31130, plain, (![B_2207]: (m1_subset_1(k3_xboole_0(B_2207, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_31124])).
% 17.61/10.21  tff(c_12, plain, (![A_14]: (~v1_subset_1('#skF_1'(A_14), A_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 17.61/10.21  tff(c_14, plain, (![A_14]: (m1_subset_1('#skF_1'(A_14), k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 17.61/10.21  tff(c_14611, plain, (![B_1224, A_1225]: (v1_subset_1(B_1224, A_1225) | B_1224=A_1225 | ~m1_subset_1(B_1224, k1_zfmisc_1(A_1225)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 17.61/10.21  tff(c_14620, plain, (![A_14]: (v1_subset_1('#skF_1'(A_14), A_14) | '#skF_1'(A_14)=A_14)), inference(resolution, [status(thm)], [c_14, c_14611])).
% 17.61/10.21  tff(c_14628, plain, (![A_14]: ('#skF_1'(A_14)=A_14)), inference(negUnitSimplification, [status(thm)], [c_12, c_14620])).
% 17.61/10.21  tff(c_14636, plain, (![A_14]: (m1_subset_1(A_14, k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_14628, c_14])).
% 17.61/10.21  tff(c_31078, plain, (![A_14, B_2198]: (k9_subset_1(A_14, B_2198, A_14)=k3_xboole_0(B_2198, A_14))), inference(resolution, [status(thm)], [c_14636, c_31066])).
% 17.61/10.21  tff(c_15232, plain, (![A_1295, B_1296, C_1297]: (m1_subset_1(k9_subset_1(A_1295, B_1296, C_1297), k1_zfmisc_1(A_1295)) | ~m1_subset_1(C_1297, k1_zfmisc_1(A_1295)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 17.61/10.21  tff(c_16, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 17.61/10.21  tff(c_31297, plain, (![A_2230, B_2231, C_2232]: (r1_tarski(k9_subset_1(A_2230, B_2231, C_2232), A_2230) | ~m1_subset_1(C_2232, k1_zfmisc_1(A_2230)))), inference(resolution, [status(thm)], [c_15232, c_16])).
% 17.61/10.21  tff(c_24, plain, (![C_26, A_20, B_24]: (v2_tex_2(C_26, A_20) | ~v2_tex_2(B_24, A_20) | ~r1_tarski(C_26, B_24) | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 17.61/10.21  tff(c_36164, plain, (![A_2546, B_2547, C_2548, A_2549]: (v2_tex_2(k9_subset_1(A_2546, B_2547, C_2548), A_2549) | ~v2_tex_2(A_2546, A_2549) | ~m1_subset_1(k9_subset_1(A_2546, B_2547, C_2548), k1_zfmisc_1(u1_struct_0(A_2549))) | ~m1_subset_1(A_2546, k1_zfmisc_1(u1_struct_0(A_2549))) | ~l1_pre_topc(A_2549) | ~m1_subset_1(C_2548, k1_zfmisc_1(A_2546)))), inference(resolution, [status(thm)], [c_31297, c_24])).
% 17.61/10.21  tff(c_36200, plain, (![A_14, B_2198, A_2549]: (v2_tex_2(k9_subset_1(A_14, B_2198, A_14), A_2549) | ~v2_tex_2(A_14, A_2549) | ~m1_subset_1(k3_xboole_0(B_2198, A_14), k1_zfmisc_1(u1_struct_0(A_2549))) | ~m1_subset_1(A_14, k1_zfmisc_1(u1_struct_0(A_2549))) | ~l1_pre_topc(A_2549) | ~m1_subset_1(A_14, k1_zfmisc_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_31078, c_36164])).
% 17.61/10.21  tff(c_55333, plain, (![B_3309, A_3310, A_3311]: (v2_tex_2(k3_xboole_0(B_3309, A_3310), A_3311) | ~v2_tex_2(A_3310, A_3311) | ~m1_subset_1(k3_xboole_0(B_3309, A_3310), k1_zfmisc_1(u1_struct_0(A_3311))) | ~m1_subset_1(A_3310, k1_zfmisc_1(u1_struct_0(A_3311))) | ~l1_pre_topc(A_3311))), inference(demodulation, [status(thm), theory('equality')], [c_14636, c_31078, c_36200])).
% 17.61/10.21  tff(c_55387, plain, (![B_2207]: (v2_tex_2(k3_xboole_0(B_2207, '#skF_4'), '#skF_2') | ~v2_tex_2('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_31130, c_55333])).
% 17.61/10.21  tff(c_55438, plain, (![B_2207]: (v2_tex_2(k3_xboole_0(B_2207, '#skF_4'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_14500, c_55387])).
% 17.61/10.21  tff(c_31080, plain, (![B_2198]: (k9_subset_1(u1_struct_0('#skF_2'), B_2198, '#skF_4')=k3_xboole_0(B_2198, '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_31066])).
% 17.61/10.21  tff(c_31117, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_31080, c_26])).
% 17.61/10.21  tff(c_55450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55438, c_31117])).
% 17.61/10.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.61/10.21  
% 17.61/10.21  Inference rules
% 17.61/10.21  ----------------------
% 17.61/10.21  #Ref     : 0
% 17.61/10.21  #Sup     : 11877
% 17.61/10.21  #Fact    : 0
% 17.61/10.21  #Define  : 0
% 17.61/10.21  #Split   : 10
% 17.61/10.21  #Chain   : 0
% 17.61/10.21  #Close   : 0
% 17.61/10.21  
% 17.61/10.21  Ordering : KBO
% 17.61/10.21  
% 17.61/10.21  Simplification rules
% 17.61/10.21  ----------------------
% 17.61/10.21  #Subsume      : 542
% 17.61/10.21  #Demod        : 2846
% 17.61/10.21  #Tautology    : 1691
% 17.61/10.21  #SimpNegUnit  : 21
% 17.61/10.21  #BackRed      : 62
% 17.61/10.21  
% 17.61/10.21  #Partial instantiations: 0
% 17.61/10.21  #Strategies tried      : 1
% 17.61/10.21  
% 17.61/10.21  Timing (in seconds)
% 17.61/10.21  ----------------------
% 17.61/10.21  Preprocessing        : 0.30
% 17.61/10.21  Parsing              : 0.16
% 17.61/10.21  CNF conversion       : 0.02
% 17.61/10.21  Main loop            : 9.14
% 17.61/10.21  Inferencing          : 1.71
% 17.61/10.21  Reduction            : 3.23
% 17.61/10.21  Demodulation         : 2.69
% 17.61/10.21  BG Simplification    : 0.22
% 17.61/10.21  Subsumption          : 3.38
% 17.61/10.21  Abstraction          : 0.28
% 17.61/10.21  MUC search           : 0.00
% 17.61/10.21  Cooper               : 0.00
% 17.61/10.21  Total                : 9.48
% 17.61/10.21  Index Insertion      : 0.00
% 17.61/10.21  Index Deletion       : 0.00
% 17.61/10.21  Index Matching       : 0.00
% 17.61/10.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
