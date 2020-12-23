%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:10 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   60 (  96 expanded)
%              Number of leaves         :   27 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   87 ( 179 expanded)
%              Number of equality atoms :   26 (  54 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
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
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_55,axiom,(
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

tff(c_24,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_10,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_84,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_99,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_84])).

tff(c_102,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_99])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_53])).

tff(c_28,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_26,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_144,plain,(
    ! [B_36,A_37] :
      ( v2_tops_1(B_36,A_37)
      | ~ v3_tops_1(B_36,A_37)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_147,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_144])).

tff(c_150,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_147])).

tff(c_193,plain,(
    ! [A_40,B_41] :
      ( k1_tops_1(A_40,B_41) = k1_xboole_0
      | ~ v2_tops_1(B_41,A_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_196,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_193])).

tff(c_199,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_150,c_196])).

tff(c_303,plain,(
    ! [B_48,A_49,C_50] :
      ( r1_tarski(B_48,k1_tops_1(A_49,C_50))
      | ~ r1_tarski(B_48,C_50)
      | ~ v3_pre_topc(B_48,A_49)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_305,plain,(
    ! [B_48] :
      ( r1_tarski(B_48,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_48,'#skF_2')
      | ~ v3_pre_topc(B_48,'#skF_1')
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_303])).

tff(c_309,plain,(
    ! [B_51] :
      ( r1_tarski(B_51,k1_xboole_0)
      | ~ r1_tarski(B_51,'#skF_2')
      | ~ v3_pre_topc(B_51,'#skF_1')
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_199,c_305])).

tff(c_312,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_309])).

tff(c_315,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6,c_312])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_324,plain,(
    k3_xboole_0('#skF_2',k1_xboole_0) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_315,c_8])).

tff(c_14,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_124,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k3_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,k4_xboole_0(A_34,B_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_84])).

tff(c_152,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k3_xboole_0(A_38,k4_xboole_0(A_38,B_39))) = k3_xboole_0(A_38,k3_xboole_0(A_38,B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_14])).

tff(c_164,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k3_xboole_0(A_38,k3_xboole_0(A_38,B_39))) = k3_xboole_0(A_38,k3_xboole_0(A_38,k4_xboole_0(A_38,B_39))) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_14])).

tff(c_328,plain,(
    k3_xboole_0('#skF_2',k3_xboole_0('#skF_2',k4_xboole_0('#skF_2',k1_xboole_0))) = k4_xboole_0('#skF_2',k3_xboole_0('#skF_2','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_164])).

tff(c_338,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_57,c_57,c_57,c_12,c_328])).

tff(c_340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_338])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:29:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.25  
% 2.16/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.25  %$ v3_tops_1 > v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.16/1.25  
% 2.16/1.25  %Foreground sorts:
% 2.16/1.25  
% 2.16/1.25  
% 2.16/1.25  %Background operators:
% 2.16/1.25  
% 2.16/1.25  
% 2.16/1.25  %Foreground operators:
% 2.16/1.25  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.16/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.25  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.16/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.16/1.25  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 2.16/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.25  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.16/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.25  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.16/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.16/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.25  
% 2.16/1.26  tff(f_87, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_tops_1)).
% 2.16/1.26  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.16/1.26  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.16/1.26  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.16/1.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.16/1.26  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.16/1.26  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 2.16/1.26  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 2.16/1.26  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 2.16/1.26  tff(c_24, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.16/1.26  tff(c_10, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.26  tff(c_12, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.16/1.26  tff(c_84, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.16/1.26  tff(c_99, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_84])).
% 2.16/1.26  tff(c_102, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_99])).
% 2.16/1.26  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.26  tff(c_53, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.26  tff(c_57, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_53])).
% 2.16/1.26  tff(c_28, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.16/1.26  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.16/1.26  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.16/1.26  tff(c_26, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.16/1.26  tff(c_144, plain, (![B_36, A_37]: (v2_tops_1(B_36, A_37) | ~v3_tops_1(B_36, A_37) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.16/1.26  tff(c_147, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_144])).
% 2.16/1.26  tff(c_150, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_147])).
% 2.16/1.26  tff(c_193, plain, (![A_40, B_41]: (k1_tops_1(A_40, B_41)=k1_xboole_0 | ~v2_tops_1(B_41, A_40) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.16/1.26  tff(c_196, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_193])).
% 2.16/1.26  tff(c_199, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_150, c_196])).
% 2.16/1.26  tff(c_303, plain, (![B_48, A_49, C_50]: (r1_tarski(B_48, k1_tops_1(A_49, C_50)) | ~r1_tarski(B_48, C_50) | ~v3_pre_topc(B_48, A_49) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.16/1.26  tff(c_305, plain, (![B_48]: (r1_tarski(B_48, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_48, '#skF_2') | ~v3_pre_topc(B_48, '#skF_1') | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_303])).
% 2.16/1.26  tff(c_309, plain, (![B_51]: (r1_tarski(B_51, k1_xboole_0) | ~r1_tarski(B_51, '#skF_2') | ~v3_pre_topc(B_51, '#skF_1') | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_199, c_305])).
% 2.16/1.26  tff(c_312, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_2', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_309])).
% 2.16/1.26  tff(c_315, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6, c_312])).
% 2.16/1.26  tff(c_8, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.26  tff(c_324, plain, (k3_xboole_0('#skF_2', k1_xboole_0)='#skF_2'), inference(resolution, [status(thm)], [c_315, c_8])).
% 2.16/1.26  tff(c_14, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.16/1.26  tff(c_124, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k3_xboole_0(A_34, B_35))=k3_xboole_0(A_34, k4_xboole_0(A_34, B_35)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_84])).
% 2.16/1.26  tff(c_152, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k3_xboole_0(A_38, k4_xboole_0(A_38, B_39)))=k3_xboole_0(A_38, k3_xboole_0(A_38, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_124, c_14])).
% 2.16/1.26  tff(c_164, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k3_xboole_0(A_38, k3_xboole_0(A_38, B_39)))=k3_xboole_0(A_38, k3_xboole_0(A_38, k4_xboole_0(A_38, B_39))))), inference(superposition, [status(thm), theory('equality')], [c_152, c_14])).
% 2.16/1.26  tff(c_328, plain, (k3_xboole_0('#skF_2', k3_xboole_0('#skF_2', k4_xboole_0('#skF_2', k1_xboole_0)))=k4_xboole_0('#skF_2', k3_xboole_0('#skF_2', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_324, c_164])).
% 2.16/1.26  tff(c_338, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_57, c_57, c_57, c_12, c_328])).
% 2.16/1.26  tff(c_340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_338])).
% 2.16/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.26  
% 2.16/1.26  Inference rules
% 2.16/1.26  ----------------------
% 2.16/1.26  #Ref     : 0
% 2.16/1.26  #Sup     : 75
% 2.16/1.26  #Fact    : 0
% 2.16/1.26  #Define  : 0
% 2.16/1.26  #Split   : 0
% 2.16/1.26  #Chain   : 0
% 2.16/1.26  #Close   : 0
% 2.16/1.26  
% 2.16/1.26  Ordering : KBO
% 2.16/1.26  
% 2.16/1.26  Simplification rules
% 2.16/1.26  ----------------------
% 2.16/1.26  #Subsume      : 0
% 2.16/1.26  #Demod        : 69
% 2.16/1.26  #Tautology    : 47
% 2.16/1.26  #SimpNegUnit  : 2
% 2.16/1.26  #BackRed      : 0
% 2.16/1.26  
% 2.16/1.26  #Partial instantiations: 0
% 2.16/1.26  #Strategies tried      : 1
% 2.16/1.26  
% 2.16/1.26  Timing (in seconds)
% 2.16/1.26  ----------------------
% 2.16/1.27  Preprocessing        : 0.29
% 2.16/1.27  Parsing              : 0.16
% 2.16/1.27  CNF conversion       : 0.02
% 2.16/1.27  Main loop            : 0.20
% 2.16/1.27  Inferencing          : 0.08
% 2.16/1.27  Reduction            : 0.07
% 2.16/1.27  Demodulation         : 0.06
% 2.16/1.27  BG Simplification    : 0.01
% 2.16/1.27  Subsumption          : 0.03
% 2.16/1.27  Abstraction          : 0.01
% 2.16/1.27  MUC search           : 0.00
% 2.16/1.27  Cooper               : 0.00
% 2.16/1.27  Total                : 0.52
% 2.16/1.27  Index Insertion      : 0.00
% 2.16/1.27  Index Deletion       : 0.00
% 2.16/1.27  Index Matching       : 0.00
% 2.16/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
