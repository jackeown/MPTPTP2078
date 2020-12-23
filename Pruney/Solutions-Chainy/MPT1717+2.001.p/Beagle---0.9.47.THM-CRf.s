%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:40 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   45 (  83 expanded)
%              Number of leaves         :   20 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  129 ( 274 expanded)
%              Number of equality atoms :   11 (  30 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_tsep_1,type,(
    k2_tsep_1: ( $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => k2_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tmap_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_110,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( ~ r1_tsep_1(B,C)
               => ( ( m1_pre_topc(B,C)
                   => k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) )
                  & ( k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                   => m1_pre_topc(B,C) )
                  & ( m1_pre_topc(C,B)
                   => k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) )
                  & ( k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
                   => m1_pre_topc(C,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tsep_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( m1_pre_topc(B,C)
               => ( ~ r1_tsep_1(B,C)
                  & ~ r1_tsep_1(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_26,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [B_33,C_34,A_35] :
      ( m1_pre_topc(B_33,C_34)
      | ~ r1_tarski(u1_struct_0(B_33),u1_struct_0(C_34))
      | ~ m1_pre_topc(C_34,A_35)
      | ~ m1_pre_topc(B_33,A_35)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_79,plain,(
    ! [B_36,A_37] :
      ( m1_pre_topc(B_36,B_36)
      | ~ m1_pre_topc(B_36,A_37)
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37) ) ),
    inference(resolution,[status(thm)],[c_6,c_71])).

tff(c_81,plain,
    ( m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_79])).

tff(c_84,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_81])).

tff(c_95,plain,(
    ! [A_44,B_45,C_46] :
      ( k2_tsep_1(A_44,B_45,C_46) = g1_pre_topc(u1_struct_0(B_45),u1_pre_topc(B_45))
      | ~ m1_pre_topc(B_45,C_46)
      | r1_tsep_1(B_45,C_46)
      | ~ m1_pre_topc(C_46,A_44)
      | v2_struct_0(C_46)
      | ~ m1_pre_topc(B_45,A_44)
      | v2_struct_0(B_45)
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_99,plain,(
    ! [B_45] :
      ( g1_pre_topc(u1_struct_0(B_45),u1_pre_topc(B_45)) = k2_tsep_1('#skF_1',B_45,'#skF_2')
      | ~ m1_pre_topc(B_45,'#skF_2')
      | r1_tsep_1(B_45,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_45,'#skF_1')
      | v2_struct_0(B_45)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_95])).

tff(c_104,plain,(
    ! [B_45] :
      ( g1_pre_topc(u1_struct_0(B_45),u1_pre_topc(B_45)) = k2_tsep_1('#skF_1',B_45,'#skF_2')
      | ~ m1_pre_topc(B_45,'#skF_2')
      | r1_tsep_1(B_45,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_45,'#skF_1')
      | v2_struct_0(B_45)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_99])).

tff(c_106,plain,(
    ! [B_47] :
      ( g1_pre_topc(u1_struct_0(B_47),u1_pre_topc(B_47)) = k2_tsep_1('#skF_1',B_47,'#skF_2')
      | ~ m1_pre_topc(B_47,'#skF_2')
      | r1_tsep_1(B_47,'#skF_2')
      | ~ m1_pre_topc(B_47,'#skF_1')
      | v2_struct_0(B_47) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_28,c_104])).

tff(c_24,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k2_tsep_1('#skF_1','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_112,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_2')
    | r1_tsep_1('#skF_2','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_24])).

tff(c_119,plain,
    ( r1_tsep_1('#skF_2','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_84,c_112])).

tff(c_120,plain,(
    r1_tsep_1('#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_119])).

tff(c_8,plain,(
    ! [C_9,B_7,A_3] :
      ( ~ r1_tsep_1(C_9,B_7)
      | ~ m1_pre_topc(B_7,C_9)
      | ~ m1_pre_topc(C_9,A_3)
      | v2_struct_0(C_9)
      | ~ m1_pre_topc(B_7,A_3)
      | v2_struct_0(B_7)
      | ~ l1_pre_topc(A_3)
      | ~ v2_pre_topc(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_123,plain,(
    ! [A_3] :
      ( ~ m1_pre_topc('#skF_2','#skF_2')
      | ~ m1_pre_topc('#skF_2',A_3)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_3)
      | ~ v2_pre_topc(A_3)
      | v2_struct_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_120,c_8])).

tff(c_128,plain,(
    ! [A_3] :
      ( ~ m1_pre_topc('#skF_2',A_3)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_3)
      | ~ v2_pre_topc(A_3)
      | v2_struct_0(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_123])).

tff(c_134,plain,(
    ! [A_48] :
      ( ~ m1_pre_topc('#skF_2',A_48)
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_128])).

tff(c_140,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_134])).

tff(c_145,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_140])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_145])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:46:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.20  
% 2.09/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.20  %$ r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_1
% 2.09/1.20  
% 2.09/1.20  %Foreground sorts:
% 2.09/1.20  
% 2.09/1.20  
% 2.09/1.20  %Background operators:
% 2.09/1.20  
% 2.09/1.20  
% 2.09/1.20  %Foreground operators:
% 2.09/1.20  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.09/1.20  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.09/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.20  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.09/1.20  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.09/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.20  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.20  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.20  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.09/1.20  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 2.09/1.20  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.09/1.20  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.09/1.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.09/1.20  
% 2.09/1.22  tff(f_126, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k2_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tmap_1)).
% 2.09/1.22  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.09/1.22  tff(f_110, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.09/1.22  tff(f_96, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => ((((m1_pre_topc(B, C) => (k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))) & ((k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => m1_pre_topc(B, C))) & (m1_pre_topc(C, B) => (k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))))) & ((k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => m1_pre_topc(C, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tsep_1)).
% 2.09/1.22  tff(f_58, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tmap_1)).
% 2.09/1.22  tff(c_34, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.09/1.22  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.09/1.22  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.09/1.22  tff(c_26, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.09/1.22  tff(c_28, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.09/1.22  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.22  tff(c_71, plain, (![B_33, C_34, A_35]: (m1_pre_topc(B_33, C_34) | ~r1_tarski(u1_struct_0(B_33), u1_struct_0(C_34)) | ~m1_pre_topc(C_34, A_35) | ~m1_pre_topc(B_33, A_35) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.09/1.22  tff(c_79, plain, (![B_36, A_37]: (m1_pre_topc(B_36, B_36) | ~m1_pre_topc(B_36, A_37) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37))), inference(resolution, [status(thm)], [c_6, c_71])).
% 2.09/1.22  tff(c_81, plain, (m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_79])).
% 2.09/1.22  tff(c_84, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_81])).
% 2.09/1.22  tff(c_95, plain, (![A_44, B_45, C_46]: (k2_tsep_1(A_44, B_45, C_46)=g1_pre_topc(u1_struct_0(B_45), u1_pre_topc(B_45)) | ~m1_pre_topc(B_45, C_46) | r1_tsep_1(B_45, C_46) | ~m1_pre_topc(C_46, A_44) | v2_struct_0(C_46) | ~m1_pre_topc(B_45, A_44) | v2_struct_0(B_45) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.09/1.22  tff(c_99, plain, (![B_45]: (g1_pre_topc(u1_struct_0(B_45), u1_pre_topc(B_45))=k2_tsep_1('#skF_1', B_45, '#skF_2') | ~m1_pre_topc(B_45, '#skF_2') | r1_tsep_1(B_45, '#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_45, '#skF_1') | v2_struct_0(B_45) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_95])).
% 2.09/1.22  tff(c_104, plain, (![B_45]: (g1_pre_topc(u1_struct_0(B_45), u1_pre_topc(B_45))=k2_tsep_1('#skF_1', B_45, '#skF_2') | ~m1_pre_topc(B_45, '#skF_2') | r1_tsep_1(B_45, '#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_45, '#skF_1') | v2_struct_0(B_45) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_99])).
% 2.09/1.22  tff(c_106, plain, (![B_47]: (g1_pre_topc(u1_struct_0(B_47), u1_pre_topc(B_47))=k2_tsep_1('#skF_1', B_47, '#skF_2') | ~m1_pre_topc(B_47, '#skF_2') | r1_tsep_1(B_47, '#skF_2') | ~m1_pre_topc(B_47, '#skF_1') | v2_struct_0(B_47))), inference(negUnitSimplification, [status(thm)], [c_34, c_28, c_104])).
% 2.09/1.22  tff(c_24, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k2_tsep_1('#skF_1', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.09/1.22  tff(c_112, plain, (~m1_pre_topc('#skF_2', '#skF_2') | r1_tsep_1('#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_106, c_24])).
% 2.09/1.22  tff(c_119, plain, (r1_tsep_1('#skF_2', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_84, c_112])).
% 2.09/1.22  tff(c_120, plain, (r1_tsep_1('#skF_2', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_28, c_119])).
% 2.09/1.22  tff(c_8, plain, (![C_9, B_7, A_3]: (~r1_tsep_1(C_9, B_7) | ~m1_pre_topc(B_7, C_9) | ~m1_pre_topc(C_9, A_3) | v2_struct_0(C_9) | ~m1_pre_topc(B_7, A_3) | v2_struct_0(B_7) | ~l1_pre_topc(A_3) | ~v2_pre_topc(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.09/1.22  tff(c_123, plain, (![A_3]: (~m1_pre_topc('#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', A_3) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_3) | ~v2_pre_topc(A_3) | v2_struct_0(A_3))), inference(resolution, [status(thm)], [c_120, c_8])).
% 2.09/1.22  tff(c_128, plain, (![A_3]: (~m1_pre_topc('#skF_2', A_3) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_3) | ~v2_pre_topc(A_3) | v2_struct_0(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_123])).
% 2.09/1.22  tff(c_134, plain, (![A_48]: (~m1_pre_topc('#skF_2', A_48) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(negUnitSimplification, [status(thm)], [c_28, c_128])).
% 2.09/1.22  tff(c_140, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_134])).
% 2.09/1.22  tff(c_145, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_140])).
% 2.09/1.22  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_145])).
% 2.09/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.22  
% 2.09/1.22  Inference rules
% 2.09/1.22  ----------------------
% 2.09/1.22  #Ref     : 0
% 2.09/1.22  #Sup     : 19
% 2.09/1.22  #Fact    : 0
% 2.09/1.22  #Define  : 0
% 2.09/1.22  #Split   : 1
% 2.09/1.22  #Chain   : 0
% 2.09/1.22  #Close   : 0
% 2.09/1.22  
% 2.09/1.22  Ordering : KBO
% 2.09/1.22  
% 2.09/1.22  Simplification rules
% 2.09/1.22  ----------------------
% 2.09/1.22  #Subsume      : 2
% 2.09/1.22  #Demod        : 17
% 2.09/1.22  #Tautology    : 8
% 2.09/1.22  #SimpNegUnit  : 7
% 2.09/1.22  #BackRed      : 0
% 2.09/1.22  
% 2.09/1.22  #Partial instantiations: 0
% 2.09/1.22  #Strategies tried      : 1
% 2.09/1.22  
% 2.09/1.22  Timing (in seconds)
% 2.09/1.22  ----------------------
% 2.09/1.22  Preprocessing        : 0.30
% 2.09/1.22  Parsing              : 0.16
% 2.09/1.22  CNF conversion       : 0.02
% 2.09/1.22  Main loop            : 0.16
% 2.09/1.22  Inferencing          : 0.06
% 2.09/1.22  Reduction            : 0.04
% 2.09/1.22  Demodulation         : 0.03
% 2.09/1.22  BG Simplification    : 0.01
% 2.09/1.22  Subsumption          : 0.04
% 2.09/1.22  Abstraction          : 0.01
% 2.09/1.22  MUC search           : 0.00
% 2.09/1.22  Cooper               : 0.00
% 2.09/1.22  Total                : 0.48
% 2.09/1.22  Index Insertion      : 0.00
% 2.09/1.22  Index Deletion       : 0.00
% 2.09/1.22  Index Matching       : 0.00
% 2.09/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
