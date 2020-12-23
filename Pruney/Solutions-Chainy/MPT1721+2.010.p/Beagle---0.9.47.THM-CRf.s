%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:45 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   51 (  77 expanded)
%              Number of leaves         :   21 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  139 ( 393 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_tsep_1,type,(
    k2_tsep_1: ( $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_127,negated_conjecture,(
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
                   => ( ( m1_pre_topc(B,D)
                        & m1_pre_topc(C,D) )
                     => ( r1_tsep_1(B,C)
                        | m1_pre_topc(k2_tsep_1(A,B,C),D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tmap_1)).

tff(f_93,axiom,(
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
                     => ( ( m1_pre_topc(B,D)
                          & m1_pre_topc(C,E) )
                       => ( r1_tsep_1(B,C)
                          | m1_pre_topc(k2_tsep_1(A,B,C),k2_tsep_1(A,D,E)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tmap_1)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => k2_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tmap_1)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_24,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_12,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_26,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_22,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_16,plain,(
    m1_pre_topc('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_14,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_20,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_18,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_126,plain,(
    ! [A_61,D_62,E_63,B_60,C_59] :
      ( m1_pre_topc(k2_tsep_1(A_61,B_60,C_59),k2_tsep_1(A_61,D_62,E_63))
      | r1_tsep_1(B_60,C_59)
      | ~ m1_pre_topc(C_59,E_63)
      | ~ m1_pre_topc(B_60,D_62)
      | ~ m1_pre_topc(E_63,A_61)
      | v2_struct_0(E_63)
      | ~ m1_pre_topc(D_62,A_61)
      | v2_struct_0(D_62)
      | ~ m1_pre_topc(C_59,A_61)
      | v2_struct_0(C_59)
      | ~ m1_pre_topc(B_60,A_61)
      | v2_struct_0(B_60)
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_35,plain,(
    ! [B_52,A_53] :
      ( l1_pre_topc(B_52)
      | ~ m1_pre_topc(B_52,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_35])).

tff(c_58,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_47])).

tff(c_67,plain,(
    ! [A_56,B_57] :
      ( k2_tsep_1(A_56,B_57,B_57) = g1_pre_topc(u1_struct_0(B_57),u1_pre_topc(B_57))
      | ~ m1_pre_topc(B_57,A_56)
      | v2_struct_0(B_57)
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_75,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = k2_tsep_1('#skF_1','#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_67])).

tff(c_92,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = k2_tsep_1('#skF_1','#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_75])).

tff(c_93,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = k2_tsep_1('#skF_1','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_20,c_92])).

tff(c_4,plain,(
    ! [B_6,A_4] :
      ( m1_pre_topc(B_6,A_4)
      | ~ m1_pre_topc(B_6,g1_pre_topc(u1_struct_0(A_4),u1_pre_topc(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_110,plain,(
    ! [B_6] :
      ( m1_pre_topc(B_6,'#skF_4')
      | ~ m1_pre_topc(B_6,k2_tsep_1('#skF_1','#skF_4','#skF_4'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_4])).

tff(c_114,plain,(
    ! [B_6] :
      ( m1_pre_topc(B_6,'#skF_4')
      | ~ m1_pre_topc(B_6,k2_tsep_1('#skF_1','#skF_4','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_110])).

tff(c_130,plain,(
    ! [B_60,C_59] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_60,C_59),'#skF_4')
      | r1_tsep_1(B_60,C_59)
      | ~ m1_pre_topc(C_59,'#skF_4')
      | ~ m1_pre_topc(B_60,'#skF_4')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_59,'#skF_1')
      | v2_struct_0(C_59)
      | ~ m1_pre_topc(B_60,'#skF_1')
      | v2_struct_0(B_60)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_126,c_114])).

tff(c_138,plain,(
    ! [B_60,C_59] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_60,C_59),'#skF_4')
      | r1_tsep_1(B_60,C_59)
      | ~ m1_pre_topc(C_59,'#skF_4')
      | ~ m1_pre_topc(B_60,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_59,'#skF_1')
      | v2_struct_0(C_59)
      | ~ m1_pre_topc(B_60,'#skF_1')
      | v2_struct_0(B_60)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_18,c_130])).

tff(c_164,plain,(
    ! [B_66,C_67] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_66,C_67),'#skF_4')
      | r1_tsep_1(B_66,C_67)
      | ~ m1_pre_topc(C_67,'#skF_4')
      | ~ m1_pre_topc(B_66,'#skF_4')
      | ~ m1_pre_topc(C_67,'#skF_1')
      | v2_struct_0(C_67)
      | ~ m1_pre_topc(B_66,'#skF_1')
      | v2_struct_0(B_66) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_20,c_138])).

tff(c_10,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_172,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_164,c_10])).

tff(c_182,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_16,c_14,c_172])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_24,c_12,c_182])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.20  
% 1.98/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.20  %$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.98/1.20  
% 1.98/1.20  %Foreground sorts:
% 1.98/1.20  
% 1.98/1.20  
% 1.98/1.20  %Background operators:
% 1.98/1.20  
% 1.98/1.20  
% 1.98/1.20  %Foreground operators:
% 1.98/1.20  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.98/1.20  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.98/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.20  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 1.98/1.20  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.98/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.20  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.98/1.20  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 1.98/1.20  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.98/1.20  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 1.98/1.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.98/1.20  
% 1.98/1.21  tff(f_127, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((m1_pre_topc(B, D) & m1_pre_topc(C, D)) => (r1_tsep_1(B, C) | m1_pre_topc(k2_tsep_1(A, B, C), D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tmap_1)).
% 1.98/1.21  tff(f_93, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(B, D) & m1_pre_topc(C, E)) => (r1_tsep_1(B, C) | m1_pre_topc(k2_tsep_1(A, B, C), k2_tsep_1(A, D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tmap_1)).
% 1.98/1.21  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 1.98/1.21  tff(f_54, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k2_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tmap_1)).
% 1.98/1.21  tff(f_39, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 1.98/1.21  tff(c_28, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 1.98/1.21  tff(c_24, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 1.98/1.21  tff(c_12, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 1.98/1.21  tff(c_26, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 1.98/1.21  tff(c_22, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 1.98/1.21  tff(c_16, plain, (m1_pre_topc('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 1.98/1.21  tff(c_14, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 1.98/1.21  tff(c_34, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 1.98/1.21  tff(c_20, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 1.98/1.21  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 1.98/1.21  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 1.98/1.21  tff(c_18, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 1.98/1.21  tff(c_126, plain, (![A_61, D_62, E_63, B_60, C_59]: (m1_pre_topc(k2_tsep_1(A_61, B_60, C_59), k2_tsep_1(A_61, D_62, E_63)) | r1_tsep_1(B_60, C_59) | ~m1_pre_topc(C_59, E_63) | ~m1_pre_topc(B_60, D_62) | ~m1_pre_topc(E_63, A_61) | v2_struct_0(E_63) | ~m1_pre_topc(D_62, A_61) | v2_struct_0(D_62) | ~m1_pre_topc(C_59, A_61) | v2_struct_0(C_59) | ~m1_pre_topc(B_60, A_61) | v2_struct_0(B_60) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.98/1.21  tff(c_35, plain, (![B_52, A_53]: (l1_pre_topc(B_52) | ~m1_pre_topc(B_52, A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.98/1.21  tff(c_47, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_35])).
% 1.98/1.21  tff(c_58, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_47])).
% 1.98/1.21  tff(c_67, plain, (![A_56, B_57]: (k2_tsep_1(A_56, B_57, B_57)=g1_pre_topc(u1_struct_0(B_57), u1_pre_topc(B_57)) | ~m1_pre_topc(B_57, A_56) | v2_struct_0(B_57) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.98/1.21  tff(c_75, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=k2_tsep_1('#skF_1', '#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_67])).
% 1.98/1.21  tff(c_92, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=k2_tsep_1('#skF_1', '#skF_4', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_75])).
% 1.98/1.21  tff(c_93, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=k2_tsep_1('#skF_1', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_20, c_92])).
% 1.98/1.21  tff(c_4, plain, (![B_6, A_4]: (m1_pre_topc(B_6, A_4) | ~m1_pre_topc(B_6, g1_pre_topc(u1_struct_0(A_4), u1_pre_topc(A_4))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.98/1.21  tff(c_110, plain, (![B_6]: (m1_pre_topc(B_6, '#skF_4') | ~m1_pre_topc(B_6, k2_tsep_1('#skF_1', '#skF_4', '#skF_4')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_4])).
% 1.98/1.21  tff(c_114, plain, (![B_6]: (m1_pre_topc(B_6, '#skF_4') | ~m1_pre_topc(B_6, k2_tsep_1('#skF_1', '#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_110])).
% 1.98/1.21  tff(c_130, plain, (![B_60, C_59]: (m1_pre_topc(k2_tsep_1('#skF_1', B_60, C_59), '#skF_4') | r1_tsep_1(B_60, C_59) | ~m1_pre_topc(C_59, '#skF_4') | ~m1_pre_topc(B_60, '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc(C_59, '#skF_1') | v2_struct_0(C_59) | ~m1_pre_topc(B_60, '#skF_1') | v2_struct_0(B_60) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_126, c_114])).
% 1.98/1.21  tff(c_138, plain, (![B_60, C_59]: (m1_pre_topc(k2_tsep_1('#skF_1', B_60, C_59), '#skF_4') | r1_tsep_1(B_60, C_59) | ~m1_pre_topc(C_59, '#skF_4') | ~m1_pre_topc(B_60, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(C_59, '#skF_1') | v2_struct_0(C_59) | ~m1_pre_topc(B_60, '#skF_1') | v2_struct_0(B_60) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_18, c_130])).
% 1.98/1.21  tff(c_164, plain, (![B_66, C_67]: (m1_pre_topc(k2_tsep_1('#skF_1', B_66, C_67), '#skF_4') | r1_tsep_1(B_66, C_67) | ~m1_pre_topc(C_67, '#skF_4') | ~m1_pre_topc(B_66, '#skF_4') | ~m1_pre_topc(C_67, '#skF_1') | v2_struct_0(C_67) | ~m1_pre_topc(B_66, '#skF_1') | v2_struct_0(B_66))), inference(negUnitSimplification, [status(thm)], [c_34, c_20, c_138])).
% 1.98/1.21  tff(c_10, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 1.98/1.21  tff(c_172, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_164, c_10])).
% 1.98/1.21  tff(c_182, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_16, c_14, c_172])).
% 1.98/1.21  tff(c_184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_24, c_12, c_182])).
% 1.98/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.21  
% 1.98/1.21  Inference rules
% 1.98/1.21  ----------------------
% 1.98/1.21  #Ref     : 0
% 1.98/1.21  #Sup     : 27
% 1.98/1.21  #Fact    : 0
% 1.98/1.21  #Define  : 0
% 1.98/1.21  #Split   : 2
% 1.98/1.21  #Chain   : 0
% 1.98/1.21  #Close   : 0
% 1.98/1.21  
% 1.98/1.21  Ordering : KBO
% 1.98/1.21  
% 1.98/1.21  Simplification rules
% 1.98/1.21  ----------------------
% 1.98/1.21  #Subsume      : 2
% 1.98/1.21  #Demod        : 35
% 1.98/1.21  #Tautology    : 8
% 1.98/1.21  #SimpNegUnit  : 10
% 1.98/1.21  #BackRed      : 0
% 1.98/1.21  
% 1.98/1.21  #Partial instantiations: 0
% 1.98/1.21  #Strategies tried      : 1
% 1.98/1.21  
% 1.98/1.21  Timing (in seconds)
% 1.98/1.21  ----------------------
% 1.98/1.22  Preprocessing        : 0.28
% 1.98/1.22  Parsing              : 0.16
% 1.98/1.22  CNF conversion       : 0.02
% 1.98/1.22  Main loop            : 0.18
% 1.98/1.22  Inferencing          : 0.07
% 1.98/1.22  Reduction            : 0.06
% 1.98/1.22  Demodulation         : 0.04
% 1.98/1.22  BG Simplification    : 0.01
% 1.98/1.22  Subsumption          : 0.03
% 1.98/1.22  Abstraction          : 0.01
% 1.98/1.22  MUC search           : 0.00
% 1.98/1.22  Cooper               : 0.00
% 1.98/1.22  Total                : 0.49
% 1.98/1.22  Index Insertion      : 0.00
% 1.98/1.22  Index Deletion       : 0.00
% 1.98/1.22  Index Matching       : 0.00
% 1.98/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
