%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:10 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   58 (  96 expanded)
%              Number of leaves         :   26 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 240 expanded)
%              Number of equality atoms :    9 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & v2_tops_1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v1_xboole_0(k1_tops_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_tops_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_160,plain,(
    ! [B_50,A_51,C_52] :
      ( r1_tarski(B_50,k1_tops_1(A_51,C_52))
      | ~ r1_tarski(B_50,C_52)
      | ~ v3_pre_topc(B_50,A_51)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_203,plain,(
    ! [B_59,A_60] :
      ( r1_tarski(B_59,k1_tops_1(A_60,k1_xboole_0))
      | ~ r1_tarski(B_59,k1_xboole_0)
      | ~ v3_pre_topc(B_59,A_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_10,c_160])).

tff(c_210,plain,
    ( r1_tarski('#skF_2',k1_tops_1('#skF_1',k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0)
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_203])).

tff(c_218,plain,
    ( r1_tarski('#skF_2',k1_tops_1('#skF_1',k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_210])).

tff(c_222,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_94,plain,(
    ! [B_43,A_44] :
      ( v2_tops_1(B_43,A_44)
      | ~ v3_tops_1(B_43,A_44)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_101,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_94])).

tff(c_109,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_101])).

tff(c_129,plain,(
    ! [A_48,B_49] :
      ( v1_xboole_0(k1_tops_1(A_48,B_49))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ v2_tops_1(B_49,A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_136,plain,
    ( v1_xboole_0(k1_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_129])).

tff(c_144,plain,(
    v1_xboole_0(k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_109,c_136])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_149,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_144,c_2])).

tff(c_165,plain,(
    ! [B_50] :
      ( r1_tarski(B_50,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_50,'#skF_2')
      | ~ v3_pre_topc(B_50,'#skF_1')
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_160])).

tff(c_224,plain,(
    ! [B_62] :
      ( r1_tarski(B_62,k1_xboole_0)
      | ~ r1_tarski(B_62,'#skF_2')
      | ~ v3_pre_topc(B_62,'#skF_1')
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_149,c_165])).

tff(c_231,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_224])).

tff(c_239,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_8,c_231])).

tff(c_241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_239])).

tff(c_243,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_39,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_47,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(resolution,[status(thm)],[c_10,c_39])).

tff(c_54,plain,(
    ! [B_31,A_32] :
      ( B_31 = A_32
      | ~ r1_tarski(B_31,A_32)
      | ~ r1_tarski(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_47,c_54])).

tff(c_246,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_243,c_62])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_246])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.39  
% 2.25/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.39  %$ v3_tops_1 > v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.40/1.39  
% 2.40/1.39  %Foreground sorts:
% 2.40/1.39  
% 2.40/1.39  
% 2.40/1.39  %Background operators:
% 2.40/1.39  
% 2.40/1.39  
% 2.40/1.39  %Foreground operators:
% 2.40/1.39  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.40/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.40/1.39  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.40/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.40/1.39  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 2.40/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/1.39  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.40/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.40/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.40/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.40/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.40/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.40/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.40/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.40/1.39  
% 2.40/1.42  tff(f_92, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_tops_1)).
% 2.40/1.42  tff(f_37, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.40/1.42  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 2.40/1.42  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.40/1.42  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 2.40/1.42  tff(f_55, axiom, (![A, B]: (((l1_pre_topc(A) & v2_tops_1(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v1_xboole_0(k1_tops_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc13_tops_1)).
% 2.40/1.42  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.40/1.42  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.40/1.42  tff(c_24, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.40/1.42  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.40/1.42  tff(c_28, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.40/1.42  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.40/1.42  tff(c_10, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.40/1.42  tff(c_160, plain, (![B_50, A_51, C_52]: (r1_tarski(B_50, k1_tops_1(A_51, C_52)) | ~r1_tarski(B_50, C_52) | ~v3_pre_topc(B_50, A_51) | ~m1_subset_1(C_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.40/1.42  tff(c_203, plain, (![B_59, A_60]: (r1_tarski(B_59, k1_tops_1(A_60, k1_xboole_0)) | ~r1_tarski(B_59, k1_xboole_0) | ~v3_pre_topc(B_59, A_60) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_10, c_160])).
% 2.40/1.42  tff(c_210, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0) | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_203])).
% 2.40/1.42  tff(c_218, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_210])).
% 2.40/1.42  tff(c_222, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_218])).
% 2.40/1.42  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.40/1.42  tff(c_26, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.40/1.42  tff(c_94, plain, (![B_43, A_44]: (v2_tops_1(B_43, A_44) | ~v3_tops_1(B_43, A_44) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.40/1.42  tff(c_101, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_94])).
% 2.40/1.42  tff(c_109, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_101])).
% 2.40/1.42  tff(c_129, plain, (![A_48, B_49]: (v1_xboole_0(k1_tops_1(A_48, B_49)) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~v2_tops_1(B_49, A_48) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.40/1.42  tff(c_136, plain, (v1_xboole_0(k1_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_129])).
% 2.40/1.42  tff(c_144, plain, (v1_xboole_0(k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_109, c_136])).
% 2.40/1.42  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.40/1.42  tff(c_149, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_144, c_2])).
% 2.40/1.42  tff(c_165, plain, (![B_50]: (r1_tarski(B_50, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_50, '#skF_2') | ~v3_pre_topc(B_50, '#skF_1') | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_160])).
% 2.40/1.42  tff(c_224, plain, (![B_62]: (r1_tarski(B_62, k1_xboole_0) | ~r1_tarski(B_62, '#skF_2') | ~v3_pre_topc(B_62, '#skF_1') | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_149, c_165])).
% 2.40/1.42  tff(c_231, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_2', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_224])).
% 2.40/1.42  tff(c_239, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_8, c_231])).
% 2.40/1.42  tff(c_241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_222, c_239])).
% 2.40/1.42  tff(c_243, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_218])).
% 2.40/1.42  tff(c_39, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~m1_subset_1(A_26, k1_zfmisc_1(B_27)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.40/1.42  tff(c_47, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(resolution, [status(thm)], [c_10, c_39])).
% 2.40/1.42  tff(c_54, plain, (![B_31, A_32]: (B_31=A_32 | ~r1_tarski(B_31, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.40/1.42  tff(c_62, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_47, c_54])).
% 2.40/1.42  tff(c_246, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_243, c_62])).
% 2.40/1.42  tff(c_252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_246])).
% 2.40/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.42  
% 2.40/1.42  Inference rules
% 2.40/1.42  ----------------------
% 2.40/1.42  #Ref     : 0
% 2.40/1.42  #Sup     : 40
% 2.40/1.42  #Fact    : 0
% 2.40/1.42  #Define  : 0
% 2.40/1.42  #Split   : 2
% 2.40/1.42  #Chain   : 0
% 2.40/1.42  #Close   : 0
% 2.40/1.42  
% 2.40/1.42  Ordering : KBO
% 2.40/1.42  
% 2.40/1.42  Simplification rules
% 2.40/1.42  ----------------------
% 2.40/1.42  #Subsume      : 2
% 2.40/1.42  #Demod        : 22
% 2.40/1.42  #Tautology    : 11
% 2.40/1.42  #SimpNegUnit  : 2
% 2.40/1.42  #BackRed      : 1
% 2.40/1.42  
% 2.40/1.42  #Partial instantiations: 0
% 2.40/1.42  #Strategies tried      : 1
% 2.40/1.42  
% 2.40/1.42  Timing (in seconds)
% 2.40/1.42  ----------------------
% 2.40/1.42  Preprocessing        : 0.29
% 2.40/1.42  Parsing              : 0.16
% 2.40/1.42  CNF conversion       : 0.02
% 2.40/1.42  Main loop            : 0.26
% 2.40/1.42  Inferencing          : 0.10
% 2.40/1.42  Reduction            : 0.07
% 2.40/1.42  Demodulation         : 0.05
% 2.40/1.42  BG Simplification    : 0.01
% 2.40/1.42  Subsumption          : 0.04
% 2.40/1.43  Abstraction          : 0.01
% 2.40/1.43  MUC search           : 0.00
% 2.40/1.43  Cooper               : 0.00
% 2.40/1.43  Total                : 0.60
% 2.40/1.43  Index Insertion      : 0.00
% 2.40/1.43  Index Deletion       : 0.00
% 2.40/1.43  Index Matching       : 0.00
% 2.40/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
