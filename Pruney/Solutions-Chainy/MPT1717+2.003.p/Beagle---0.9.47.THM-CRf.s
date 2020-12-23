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
% DateTime   : Thu Dec  3 10:26:40 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 121 expanded)
%              Number of leaves         :   19 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  125 ( 449 expanded)
%              Number of equality atoms :   10 (  59 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_1

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

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => k2_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tmap_1)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_101,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tsep_1)).

tff(f_59,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_20,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_30,plain,(
    ! [B_21,A_22] :
      ( l1_pre_topc(B_21)
      | ~ m1_pre_topc(B_21,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_30])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_36])).

tff(c_8,plain,(
    ! [A_11] :
      ( m1_pre_topc(A_11,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_43,plain,(
    ! [A_29,B_30,C_31] :
      ( k2_tsep_1(A_29,B_30,C_31) = g1_pre_topc(u1_struct_0(B_30),u1_pre_topc(B_30))
      | ~ m1_pre_topc(B_30,C_31)
      | r1_tsep_1(B_30,C_31)
      | ~ m1_pre_topc(C_31,A_29)
      | v2_struct_0(C_31)
      | ~ m1_pre_topc(B_30,A_29)
      | v2_struct_0(B_30)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_47,plain,(
    ! [B_30] :
      ( g1_pre_topc(u1_struct_0(B_30),u1_pre_topc(B_30)) = k2_tsep_1('#skF_1',B_30,'#skF_2')
      | ~ m1_pre_topc(B_30,'#skF_2')
      | r1_tsep_1(B_30,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_30,'#skF_1')
      | v2_struct_0(B_30)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_43])).

tff(c_51,plain,(
    ! [B_30] :
      ( g1_pre_topc(u1_struct_0(B_30),u1_pre_topc(B_30)) = k2_tsep_1('#skF_1',B_30,'#skF_2')
      | ~ m1_pre_topc(B_30,'#skF_2')
      | r1_tsep_1(B_30,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_30,'#skF_1')
      | v2_struct_0(B_30)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_47])).

tff(c_53,plain,(
    ! [B_32] :
      ( g1_pre_topc(u1_struct_0(B_32),u1_pre_topc(B_32)) = k2_tsep_1('#skF_1',B_32,'#skF_2')
      | ~ m1_pre_topc(B_32,'#skF_2')
      | r1_tsep_1(B_32,'#skF_2')
      | ~ m1_pre_topc(B_32,'#skF_1')
      | v2_struct_0(B_32) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_22,c_51])).

tff(c_18,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k2_tsep_1('#skF_1','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_59,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_2')
    | r1_tsep_1('#skF_2','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_18])).

tff(c_66,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_2')
    | r1_tsep_1('#skF_2','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_59])).

tff(c_67,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_2')
    | r1_tsep_1('#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_66])).

tff(c_69,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_72,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_69])).

tff(c_76,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_72])).

tff(c_78,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_77,plain,(
    r1_tsep_1('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_4,plain,(
    ! [C_10,B_8,A_4] :
      ( ~ r1_tsep_1(C_10,B_8)
      | ~ m1_pre_topc(B_8,C_10)
      | ~ m1_pre_topc(C_10,A_4)
      | v2_struct_0(C_10)
      | ~ m1_pre_topc(B_8,A_4)
      | v2_struct_0(B_8)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_85,plain,(
    ! [A_4] :
      ( ~ m1_pre_topc('#skF_2','#skF_2')
      | ~ m1_pre_topc('#skF_2',A_4)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4)
      | v2_struct_0(A_4) ) ),
    inference(resolution,[status(thm)],[c_77,c_4])).

tff(c_91,plain,(
    ! [A_4] :
      ( ~ m1_pre_topc('#skF_2','#skF_2')
      | ~ m1_pre_topc('#skF_2',A_4)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4)
      | v2_struct_0(A_4) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_22,c_85])).

tff(c_106,plain,(
    ! [A_36] :
      ( ~ m1_pre_topc('#skF_2',A_36)
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_91])).

tff(c_116,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_106])).

tff(c_127,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_116])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:59:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.28  
% 2.09/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.28  %$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_1
% 2.09/1.28  
% 2.09/1.28  %Foreground sorts:
% 2.09/1.28  
% 2.09/1.28  
% 2.09/1.28  %Background operators:
% 2.09/1.28  
% 2.09/1.28  
% 2.09/1.28  %Foreground operators:
% 2.09/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.09/1.28  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.28  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.09/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.09/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.28  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.09/1.28  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 2.09/1.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.09/1.28  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.09/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.09/1.28  
% 2.09/1.29  tff(f_117, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k2_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tmap_1)).
% 2.09/1.29  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.09/1.29  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 2.09/1.29  tff(f_101, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => ((((m1_pre_topc(B, C) => (k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))) & ((k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => m1_pre_topc(B, C))) & (m1_pre_topc(C, B) => (k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))))) & ((k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => m1_pre_topc(C, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tsep_1)).
% 2.09/1.29  tff(f_59, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tmap_1)).
% 2.09/1.29  tff(c_28, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.09/1.29  tff(c_26, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.09/1.29  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.09/1.29  tff(c_20, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.09/1.29  tff(c_30, plain, (![B_21, A_22]: (l1_pre_topc(B_21) | ~m1_pre_topc(B_21, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.09/1.29  tff(c_36, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_30])).
% 2.09/1.29  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_36])).
% 2.09/1.29  tff(c_8, plain, (![A_11]: (m1_pre_topc(A_11, A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.09/1.29  tff(c_22, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.09/1.29  tff(c_43, plain, (![A_29, B_30, C_31]: (k2_tsep_1(A_29, B_30, C_31)=g1_pre_topc(u1_struct_0(B_30), u1_pre_topc(B_30)) | ~m1_pre_topc(B_30, C_31) | r1_tsep_1(B_30, C_31) | ~m1_pre_topc(C_31, A_29) | v2_struct_0(C_31) | ~m1_pre_topc(B_30, A_29) | v2_struct_0(B_30) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.09/1.29  tff(c_47, plain, (![B_30]: (g1_pre_topc(u1_struct_0(B_30), u1_pre_topc(B_30))=k2_tsep_1('#skF_1', B_30, '#skF_2') | ~m1_pre_topc(B_30, '#skF_2') | r1_tsep_1(B_30, '#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_30, '#skF_1') | v2_struct_0(B_30) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_43])).
% 2.09/1.29  tff(c_51, plain, (![B_30]: (g1_pre_topc(u1_struct_0(B_30), u1_pre_topc(B_30))=k2_tsep_1('#skF_1', B_30, '#skF_2') | ~m1_pre_topc(B_30, '#skF_2') | r1_tsep_1(B_30, '#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_30, '#skF_1') | v2_struct_0(B_30) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_47])).
% 2.09/1.29  tff(c_53, plain, (![B_32]: (g1_pre_topc(u1_struct_0(B_32), u1_pre_topc(B_32))=k2_tsep_1('#skF_1', B_32, '#skF_2') | ~m1_pre_topc(B_32, '#skF_2') | r1_tsep_1(B_32, '#skF_2') | ~m1_pre_topc(B_32, '#skF_1') | v2_struct_0(B_32))), inference(negUnitSimplification, [status(thm)], [c_28, c_22, c_51])).
% 2.09/1.29  tff(c_18, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k2_tsep_1('#skF_1', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.09/1.29  tff(c_59, plain, (~m1_pre_topc('#skF_2', '#skF_2') | r1_tsep_1('#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_53, c_18])).
% 2.09/1.29  tff(c_66, plain, (~m1_pre_topc('#skF_2', '#skF_2') | r1_tsep_1('#skF_2', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_59])).
% 2.09/1.29  tff(c_67, plain, (~m1_pre_topc('#skF_2', '#skF_2') | r1_tsep_1('#skF_2', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_22, c_66])).
% 2.09/1.29  tff(c_69, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_67])).
% 2.09/1.29  tff(c_72, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_69])).
% 2.09/1.29  tff(c_76, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_72])).
% 2.09/1.29  tff(c_78, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_67])).
% 2.09/1.29  tff(c_77, plain, (r1_tsep_1('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_67])).
% 2.09/1.29  tff(c_4, plain, (![C_10, B_8, A_4]: (~r1_tsep_1(C_10, B_8) | ~m1_pre_topc(B_8, C_10) | ~m1_pre_topc(C_10, A_4) | v2_struct_0(C_10) | ~m1_pre_topc(B_8, A_4) | v2_struct_0(B_8) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.09/1.29  tff(c_85, plain, (![A_4]: (~m1_pre_topc('#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', A_4) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4) | v2_struct_0(A_4))), inference(resolution, [status(thm)], [c_77, c_4])).
% 2.09/1.29  tff(c_91, plain, (![A_4]: (~m1_pre_topc('#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', A_4) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4) | v2_struct_0(A_4))), inference(negUnitSimplification, [status(thm)], [c_22, c_22, c_85])).
% 2.09/1.29  tff(c_106, plain, (![A_36]: (~m1_pre_topc('#skF_2', A_36) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_91])).
% 2.09/1.29  tff(c_116, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_106])).
% 2.09/1.29  tff(c_127, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_116])).
% 2.09/1.29  tff(c_129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_127])).
% 2.09/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.29  
% 2.09/1.29  Inference rules
% 2.09/1.29  ----------------------
% 2.09/1.29  #Ref     : 0
% 2.09/1.29  #Sup     : 16
% 2.09/1.29  #Fact    : 0
% 2.09/1.29  #Define  : 0
% 2.09/1.29  #Split   : 1
% 2.09/1.29  #Chain   : 0
% 2.09/1.29  #Close   : 0
% 2.09/1.29  
% 2.09/1.29  Ordering : KBO
% 2.09/1.29  
% 2.09/1.29  Simplification rules
% 2.09/1.29  ----------------------
% 2.09/1.29  #Subsume      : 0
% 2.09/1.29  #Demod        : 13
% 2.09/1.29  #Tautology    : 4
% 2.09/1.29  #SimpNegUnit  : 8
% 2.09/1.29  #BackRed      : 0
% 2.09/1.29  
% 2.09/1.29  #Partial instantiations: 0
% 2.09/1.29  #Strategies tried      : 1
% 2.09/1.29  
% 2.09/1.29  Timing (in seconds)
% 2.09/1.29  ----------------------
% 2.09/1.30  Preprocessing        : 0.33
% 2.09/1.30  Parsing              : 0.18
% 2.09/1.30  CNF conversion       : 0.03
% 2.09/1.30  Main loop            : 0.16
% 2.09/1.30  Inferencing          : 0.06
% 2.09/1.30  Reduction            : 0.04
% 2.09/1.30  Demodulation         : 0.03
% 2.09/1.30  BG Simplification    : 0.02
% 2.09/1.30  Subsumption          : 0.03
% 2.09/1.30  Abstraction          : 0.01
% 2.09/1.30  MUC search           : 0.00
% 2.09/1.30  Cooper               : 0.00
% 2.09/1.30  Total                : 0.51
% 2.09/1.30  Index Insertion      : 0.00
% 2.09/1.30  Index Deletion       : 0.00
% 2.09/1.30  Index Matching       : 0.00
% 2.09/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
