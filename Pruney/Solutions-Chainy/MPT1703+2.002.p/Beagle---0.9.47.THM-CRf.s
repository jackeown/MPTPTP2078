%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:23 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   47 (  72 expanded)
%              Number of leaves         :   18 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  102 ( 235 expanded)
%              Number of equality atoms :   18 (  35 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( ( v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v2_pre_topc(C)
                  & l1_pre_topc(C) )
               => ( B = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
                 => ( m1_pre_topc(B,A)
                  <=> m1_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( l1_pre_topc(C)
             => ! [D] :
                  ( l1_pre_topc(D)
                 => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                      & g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D),u1_pre_topc(D))
                      & m1_pre_topc(C,A) )
                   => m1_pre_topc(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_pre_topc)).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_33,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_32,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_32])).

tff(c_14,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_83,plain,(
    ! [B_30,A_31] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_30),u1_pre_topc(B_30)),A_31)
      | ~ m1_pre_topc(B_30,A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_93,plain,(
    ! [A_32] :
      ( m1_pre_topc('#skF_2',A_32)
      | ~ m1_pre_topc('#skF_3',A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_83])).

tff(c_98,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_93,c_33])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_34,c_98])).

tff(c_104,plain,(
    ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_16,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_18,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_140,plain,(
    ! [A_35] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_35),u1_pre_topc(A_35)))
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_146,plain,
    ( v1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_140])).

tff(c_148,plain,(
    v1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_146])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_188,plain,(
    ! [D_43,B_44,C_45,A_46] :
      ( m1_pre_topc(D_43,B_44)
      | ~ m1_pre_topc(C_45,A_46)
      | g1_pre_topc(u1_struct_0(D_43),u1_pre_topc(D_43)) != g1_pre_topc(u1_struct_0(C_45),u1_pre_topc(C_45))
      | g1_pre_topc(u1_struct_0(B_44),u1_pre_topc(B_44)) != g1_pre_topc(u1_struct_0(A_46),u1_pre_topc(A_46))
      | ~ l1_pre_topc(D_43)
      | ~ l1_pre_topc(C_45)
      | ~ l1_pre_topc(B_44)
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_194,plain,(
    ! [D_43,B_44] :
      ( m1_pre_topc(D_43,B_44)
      | g1_pre_topc(u1_struct_0(D_43),u1_pre_topc(D_43)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | g1_pre_topc(u1_struct_0(B_44),u1_pre_topc(B_44)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(D_43)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(B_44)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_105,c_188])).

tff(c_233,plain,(
    ! [D_47,B_48] :
      ( m1_pre_topc(D_47,B_48)
      | g1_pre_topc(u1_struct_0(D_47),u1_pre_topc(D_47)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | g1_pre_topc(u1_struct_0(B_48),u1_pre_topc(B_48)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(D_47)
      | ~ l1_pre_topc(B_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_194])).

tff(c_238,plain,(
    ! [D_47,B_48] :
      ( m1_pre_topc(D_47,B_48)
      | g1_pre_topc(u1_struct_0(D_47),u1_pre_topc(D_47)) != '#skF_2'
      | g1_pre_topc(u1_struct_0(B_48),u1_pre_topc(B_48)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(D_47)
      | ~ l1_pre_topc(B_48)
      | ~ v1_pre_topc('#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_233])).

tff(c_344,plain,(
    ! [D_62,B_63] :
      ( m1_pre_topc(D_62,B_63)
      | g1_pre_topc(u1_struct_0(D_62),u1_pre_topc(D_62)) != '#skF_2'
      | g1_pre_topc(u1_struct_0(B_63),u1_pre_topc(B_63)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(D_62)
      | ~ l1_pre_topc(B_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_148,c_238])).

tff(c_348,plain,(
    ! [B_63] :
      ( m1_pre_topc('#skF_3',B_63)
      | g1_pre_topc(u1_struct_0(B_63),u1_pre_topc(B_63)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_344])).

tff(c_351,plain,(
    ! [B_63] :
      ( m1_pre_topc('#skF_3',B_63)
      | g1_pre_topc(u1_struct_0(B_63),u1_pre_topc(B_63)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(B_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_348])).

tff(c_354,plain,
    ( m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_351])).

tff(c_356,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_354])).

tff(c_358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_356])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:05:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.29  
% 2.37/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.29  %$ m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1
% 2.37/1.29  
% 2.37/1.29  %Foreground sorts:
% 2.37/1.29  
% 2.37/1.29  
% 2.37/1.29  %Background operators:
% 2.37/1.29  
% 2.37/1.29  
% 2.37/1.29  %Foreground operators:
% 2.37/1.29  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.37/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.29  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.37/1.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.37/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.37/1.29  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.37/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.29  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.37/1.29  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.37/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.37/1.29  
% 2.37/1.30  tff(f_86, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tmap_1)).
% 2.37/1.30  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 2.37/1.30  tff(f_39, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 2.37/1.30  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 2.37/1.30  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (l1_pre_topc(C) => (![D]: (l1_pre_topc(D) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D), u1_pre_topc(D)))) & m1_pre_topc(C, A)) => m1_pre_topc(D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_pre_topc)).
% 2.37/1.30  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.37/1.30  tff(c_26, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.37/1.30  tff(c_33, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_26])).
% 2.37/1.30  tff(c_32, plain, (m1_pre_topc('#skF_2', '#skF_1') | m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.37/1.30  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_33, c_32])).
% 2.37/1.30  tff(c_14, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_2'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.37/1.30  tff(c_83, plain, (![B_30, A_31]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_30), u1_pre_topc(B_30)), A_31) | ~m1_pre_topc(B_30, A_31) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.37/1.30  tff(c_93, plain, (![A_32]: (m1_pre_topc('#skF_2', A_32) | ~m1_pre_topc('#skF_3', A_32) | ~l1_pre_topc(A_32))), inference(superposition, [status(thm), theory('equality')], [c_14, c_83])).
% 2.37/1.30  tff(c_98, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_93, c_33])).
% 2.37/1.30  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_34, c_98])).
% 2.37/1.30  tff(c_104, plain, (~m1_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_26])).
% 2.37/1.30  tff(c_16, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.37/1.30  tff(c_20, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.37/1.30  tff(c_18, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.37/1.30  tff(c_140, plain, (![A_35]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_35), u1_pre_topc(A_35))) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.37/1.30  tff(c_146, plain, (v1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_140])).
% 2.37/1.30  tff(c_148, plain, (v1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_146])).
% 2.37/1.30  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.37/1.30  tff(c_105, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_26])).
% 2.37/1.30  tff(c_188, plain, (![D_43, B_44, C_45, A_46]: (m1_pre_topc(D_43, B_44) | ~m1_pre_topc(C_45, A_46) | g1_pre_topc(u1_struct_0(D_43), u1_pre_topc(D_43))!=g1_pre_topc(u1_struct_0(C_45), u1_pre_topc(C_45)) | g1_pre_topc(u1_struct_0(B_44), u1_pre_topc(B_44))!=g1_pre_topc(u1_struct_0(A_46), u1_pre_topc(A_46)) | ~l1_pre_topc(D_43) | ~l1_pre_topc(C_45) | ~l1_pre_topc(B_44) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.37/1.30  tff(c_194, plain, (![D_43, B_44]: (m1_pre_topc(D_43, B_44) | g1_pre_topc(u1_struct_0(D_43), u1_pre_topc(D_43))!=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | g1_pre_topc(u1_struct_0(B_44), u1_pre_topc(B_44))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(D_43) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(B_44) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_105, c_188])).
% 2.37/1.30  tff(c_233, plain, (![D_47, B_48]: (m1_pre_topc(D_47, B_48) | g1_pre_topc(u1_struct_0(D_47), u1_pre_topc(D_47))!=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | g1_pre_topc(u1_struct_0(B_48), u1_pre_topc(B_48))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(D_47) | ~l1_pre_topc(B_48))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_194])).
% 2.37/1.30  tff(c_238, plain, (![D_47, B_48]: (m1_pre_topc(D_47, B_48) | g1_pre_topc(u1_struct_0(D_47), u1_pre_topc(D_47))!='#skF_2' | g1_pre_topc(u1_struct_0(B_48), u1_pre_topc(B_48))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(D_47) | ~l1_pre_topc(B_48) | ~v1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_233])).
% 2.37/1.30  tff(c_344, plain, (![D_62, B_63]: (m1_pre_topc(D_62, B_63) | g1_pre_topc(u1_struct_0(D_62), u1_pre_topc(D_62))!='#skF_2' | g1_pre_topc(u1_struct_0(B_63), u1_pre_topc(B_63))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(D_62) | ~l1_pre_topc(B_63))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_148, c_238])).
% 2.37/1.30  tff(c_348, plain, (![B_63]: (m1_pre_topc('#skF_3', B_63) | g1_pre_topc(u1_struct_0(B_63), u1_pre_topc(B_63))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(B_63))), inference(superposition, [status(thm), theory('equality')], [c_14, c_344])).
% 2.37/1.30  tff(c_351, plain, (![B_63]: (m1_pre_topc('#skF_3', B_63) | g1_pre_topc(u1_struct_0(B_63), u1_pre_topc(B_63))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(B_63))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_348])).
% 2.37/1.30  tff(c_354, plain, (m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_351])).
% 2.37/1.30  tff(c_356, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_354])).
% 2.37/1.30  tff(c_358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_356])).
% 2.37/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.30  
% 2.37/1.30  Inference rules
% 2.37/1.30  ----------------------
% 2.37/1.30  #Ref     : 7
% 2.37/1.30  #Sup     : 66
% 2.37/1.30  #Fact    : 0
% 2.37/1.30  #Define  : 0
% 2.37/1.30  #Split   : 6
% 2.37/1.30  #Chain   : 0
% 2.37/1.30  #Close   : 0
% 2.37/1.30  
% 2.37/1.30  Ordering : KBO
% 2.37/1.30  
% 2.37/1.30  Simplification rules
% 2.37/1.30  ----------------------
% 2.37/1.30  #Subsume      : 6
% 2.37/1.30  #Demod        : 65
% 2.37/1.30  #Tautology    : 27
% 2.37/1.30  #SimpNegUnit  : 3
% 2.37/1.30  #BackRed      : 0
% 2.37/1.30  
% 2.37/1.30  #Partial instantiations: 0
% 2.37/1.30  #Strategies tried      : 1
% 2.37/1.30  
% 2.37/1.30  Timing (in seconds)
% 2.37/1.30  ----------------------
% 2.37/1.30  Preprocessing        : 0.27
% 2.37/1.30  Parsing              : 0.15
% 2.37/1.30  CNF conversion       : 0.02
% 2.37/1.30  Main loop            : 0.26
% 2.37/1.30  Inferencing          : 0.10
% 2.37/1.30  Reduction            : 0.07
% 2.37/1.30  Demodulation         : 0.05
% 2.37/1.30  BG Simplification    : 0.02
% 2.37/1.30  Subsumption          : 0.05
% 2.37/1.30  Abstraction          : 0.01
% 2.37/1.30  MUC search           : 0.00
% 2.37/1.30  Cooper               : 0.00
% 2.37/1.30  Total                : 0.56
% 2.37/1.30  Index Insertion      : 0.00
% 2.37/1.31  Index Deletion       : 0.00
% 2.37/1.31  Index Matching       : 0.00
% 2.37/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
