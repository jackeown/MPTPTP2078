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
% DateTime   : Thu Dec  3 10:26:43 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   49 (  74 expanded)
%              Number of leaves         :   20 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  130 ( 353 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( ( m1_pre_topc(B,C)
                        & m1_pre_topc(D,C) )
                     => m1_pre_topc(k1_tsep_1(A,B,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tmap_1)).

tff(f_91,axiom,(
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
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( ~ v2_struct_0(E)
                        & m1_pre_topc(E,A) )
                     => ( ( m1_pre_topc(B,C)
                          & m1_pre_topc(D,E) )
                       => m1_pre_topc(k1_tsep_1(A,B,D),k1_tsep_1(A,C,E)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tmap_1)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_18,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_24,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_16,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_14,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_12,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_22,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_20,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_125,plain,(
    ! [D_63,B_61,A_62,C_60,E_64] :
      ( m1_pre_topc(k1_tsep_1(A_62,B_61,D_63),k1_tsep_1(A_62,C_60,E_64))
      | ~ m1_pre_topc(D_63,E_64)
      | ~ m1_pre_topc(B_61,C_60)
      | ~ m1_pre_topc(E_64,A_62)
      | v2_struct_0(E_64)
      | ~ m1_pre_topc(D_63,A_62)
      | v2_struct_0(D_63)
      | ~ m1_pre_topc(C_60,A_62)
      | v2_struct_0(C_60)
      | ~ m1_pre_topc(B_61,A_62)
      | v2_struct_0(B_61)
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_33,plain,(
    ! [B_52,A_53] :
      ( l1_pre_topc(B_52)
      | ~ m1_pre_topc(B_52,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_33])).

tff(c_59,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_48])).

tff(c_65,plain,(
    ! [A_56,B_57] :
      ( k1_tsep_1(A_56,B_57,B_57) = g1_pre_topc(u1_struct_0(B_57),u1_pre_topc(B_57))
      | ~ m1_pre_topc(B_57,A_56)
      | v2_struct_0(B_57)
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_75,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_1','#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_65])).

tff(c_94,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_1','#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_75])).

tff(c_95,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_1','#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_22,c_94])).

tff(c_4,plain,(
    ! [B_6,A_4] :
      ( m1_pre_topc(B_6,A_4)
      | ~ m1_pre_topc(B_6,g1_pre_topc(u1_struct_0(A_4),u1_pre_topc(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_117,plain,(
    ! [B_6] :
      ( m1_pre_topc(B_6,'#skF_3')
      | ~ m1_pre_topc(B_6,k1_tsep_1('#skF_1','#skF_3','#skF_3'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_4])).

tff(c_121,plain,(
    ! [B_6] :
      ( m1_pre_topc(B_6,'#skF_3')
      | ~ m1_pre_topc(B_6,k1_tsep_1('#skF_1','#skF_3','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_117])).

tff(c_129,plain,(
    ! [B_61,D_63] :
      ( m1_pre_topc(k1_tsep_1('#skF_1',B_61,D_63),'#skF_3')
      | ~ m1_pre_topc(D_63,'#skF_3')
      | ~ m1_pre_topc(B_61,'#skF_3')
      | ~ m1_pre_topc(D_63,'#skF_1')
      | v2_struct_0(D_63)
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_61,'#skF_1')
      | v2_struct_0(B_61)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_125,c_121])).

tff(c_141,plain,(
    ! [B_61,D_63] :
      ( m1_pre_topc(k1_tsep_1('#skF_1',B_61,D_63),'#skF_3')
      | ~ m1_pre_topc(D_63,'#skF_3')
      | ~ m1_pre_topc(B_61,'#skF_3')
      | ~ m1_pre_topc(D_63,'#skF_1')
      | v2_struct_0(D_63)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_61,'#skF_1')
      | v2_struct_0(B_61)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_20,c_129])).

tff(c_189,plain,(
    ! [B_74,D_75] :
      ( m1_pre_topc(k1_tsep_1('#skF_1',B_74,D_75),'#skF_3')
      | ~ m1_pre_topc(D_75,'#skF_3')
      | ~ m1_pre_topc(B_74,'#skF_3')
      | ~ m1_pre_topc(D_75,'#skF_1')
      | v2_struct_0(D_75)
      | ~ m1_pre_topc(B_74,'#skF_1')
      | v2_struct_0(B_74) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_22,c_141])).

tff(c_10,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_197,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_189,c_10])).

tff(c_207,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_16,c_14,c_12,c_197])).

tff(c_209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_18,c_207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:50:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.27  
% 2.15/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.27  %$ m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.15/1.27  
% 2.15/1.27  %Foreground sorts:
% 2.15/1.27  
% 2.15/1.27  
% 2.15/1.27  %Background operators:
% 2.15/1.27  
% 2.15/1.27  
% 2.15/1.27  %Foreground operators:
% 2.15/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.15/1.27  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 2.15/1.27  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.15/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.27  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.15/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.15/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.27  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.15/1.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.15/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.15/1.27  
% 2.15/1.28  tff(f_123, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((m1_pre_topc(B, C) & m1_pre_topc(D, C)) => m1_pre_topc(k1_tsep_1(A, B, D), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tmap_1)).
% 2.15/1.28  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(B, C) & m1_pre_topc(D, E)) => m1_pre_topc(k1_tsep_1(A, B, D), k1_tsep_1(A, C, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tmap_1)).
% 2.15/1.28  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.15/1.28  tff(f_54, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_tmap_1)).
% 2.15/1.28  tff(f_39, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 2.15/1.28  tff(c_26, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.15/1.28  tff(c_18, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.15/1.28  tff(c_24, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.15/1.28  tff(c_16, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.15/1.28  tff(c_14, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.15/1.28  tff(c_12, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.15/1.28  tff(c_32, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.15/1.28  tff(c_22, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.15/1.28  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.15/1.28  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.15/1.28  tff(c_20, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.15/1.28  tff(c_125, plain, (![D_63, B_61, A_62, C_60, E_64]: (m1_pre_topc(k1_tsep_1(A_62, B_61, D_63), k1_tsep_1(A_62, C_60, E_64)) | ~m1_pre_topc(D_63, E_64) | ~m1_pre_topc(B_61, C_60) | ~m1_pre_topc(E_64, A_62) | v2_struct_0(E_64) | ~m1_pre_topc(D_63, A_62) | v2_struct_0(D_63) | ~m1_pre_topc(C_60, A_62) | v2_struct_0(C_60) | ~m1_pre_topc(B_61, A_62) | v2_struct_0(B_61) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.15/1.28  tff(c_33, plain, (![B_52, A_53]: (l1_pre_topc(B_52) | ~m1_pre_topc(B_52, A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.15/1.28  tff(c_48, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_33])).
% 2.15/1.28  tff(c_59, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_48])).
% 2.15/1.28  tff(c_65, plain, (![A_56, B_57]: (k1_tsep_1(A_56, B_57, B_57)=g1_pre_topc(u1_struct_0(B_57), u1_pre_topc(B_57)) | ~m1_pre_topc(B_57, A_56) | v2_struct_0(B_57) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.15/1.28  tff(c_75, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_65])).
% 2.15/1.28  tff(c_94, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_75])).
% 2.15/1.28  tff(c_95, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_1', '#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_32, c_22, c_94])).
% 2.15/1.28  tff(c_4, plain, (![B_6, A_4]: (m1_pre_topc(B_6, A_4) | ~m1_pre_topc(B_6, g1_pre_topc(u1_struct_0(A_4), u1_pre_topc(A_4))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.15/1.28  tff(c_117, plain, (![B_6]: (m1_pre_topc(B_6, '#skF_3') | ~m1_pre_topc(B_6, k1_tsep_1('#skF_1', '#skF_3', '#skF_3')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_4])).
% 2.15/1.28  tff(c_121, plain, (![B_6]: (m1_pre_topc(B_6, '#skF_3') | ~m1_pre_topc(B_6, k1_tsep_1('#skF_1', '#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_117])).
% 2.15/1.28  tff(c_129, plain, (![B_61, D_63]: (m1_pre_topc(k1_tsep_1('#skF_1', B_61, D_63), '#skF_3') | ~m1_pre_topc(D_63, '#skF_3') | ~m1_pre_topc(B_61, '#skF_3') | ~m1_pre_topc(D_63, '#skF_1') | v2_struct_0(D_63) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_61, '#skF_1') | v2_struct_0(B_61) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_125, c_121])).
% 2.15/1.28  tff(c_141, plain, (![B_61, D_63]: (m1_pre_topc(k1_tsep_1('#skF_1', B_61, D_63), '#skF_3') | ~m1_pre_topc(D_63, '#skF_3') | ~m1_pre_topc(B_61, '#skF_3') | ~m1_pre_topc(D_63, '#skF_1') | v2_struct_0(D_63) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_61, '#skF_1') | v2_struct_0(B_61) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_20, c_129])).
% 2.15/1.28  tff(c_189, plain, (![B_74, D_75]: (m1_pre_topc(k1_tsep_1('#skF_1', B_74, D_75), '#skF_3') | ~m1_pre_topc(D_75, '#skF_3') | ~m1_pre_topc(B_74, '#skF_3') | ~m1_pre_topc(D_75, '#skF_1') | v2_struct_0(D_75) | ~m1_pre_topc(B_74, '#skF_1') | v2_struct_0(B_74))), inference(negUnitSimplification, [status(thm)], [c_32, c_22, c_141])).
% 2.15/1.28  tff(c_10, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.15/1.28  tff(c_197, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_189, c_10])).
% 2.15/1.28  tff(c_207, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_16, c_14, c_12, c_197])).
% 2.15/1.28  tff(c_209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_18, c_207])).
% 2.15/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.28  
% 2.15/1.28  Inference rules
% 2.15/1.28  ----------------------
% 2.15/1.28  #Ref     : 0
% 2.15/1.28  #Sup     : 31
% 2.15/1.28  #Fact    : 0
% 2.15/1.28  #Define  : 0
% 2.15/1.28  #Split   : 1
% 2.15/1.28  #Chain   : 0
% 2.15/1.28  #Close   : 0
% 2.15/1.28  
% 2.15/1.28  Ordering : KBO
% 2.15/1.28  
% 2.15/1.28  Simplification rules
% 2.15/1.28  ----------------------
% 2.15/1.28  #Subsume      : 2
% 2.15/1.28  #Demod        : 39
% 2.15/1.28  #Tautology    : 8
% 2.15/1.28  #SimpNegUnit  : 12
% 2.15/1.28  #BackRed      : 0
% 2.15/1.28  
% 2.15/1.28  #Partial instantiations: 0
% 2.15/1.28  #Strategies tried      : 1
% 2.15/1.28  
% 2.15/1.28  Timing (in seconds)
% 2.15/1.28  ----------------------
% 2.15/1.29  Preprocessing        : 0.30
% 2.15/1.29  Parsing              : 0.17
% 2.15/1.29  CNF conversion       : 0.03
% 2.15/1.29  Main loop            : 0.21
% 2.15/1.29  Inferencing          : 0.08
% 2.15/1.29  Reduction            : 0.06
% 2.15/1.29  Demodulation         : 0.04
% 2.15/1.29  BG Simplification    : 0.01
% 2.15/1.29  Subsumption          : 0.04
% 2.15/1.29  Abstraction          : 0.01
% 2.15/1.29  MUC search           : 0.00
% 2.15/1.29  Cooper               : 0.00
% 2.15/1.29  Total                : 0.54
% 2.15/1.29  Index Insertion      : 0.00
% 2.15/1.29  Index Deletion       : 0.00
% 2.15/1.29  Index Matching       : 0.00
% 2.15/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
