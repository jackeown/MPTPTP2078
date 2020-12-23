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
% DateTime   : Thu Dec  3 10:24:37 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 109 expanded)
%              Number of leaves         :   17 (  49 expanded)
%              Depth                    :   15
%              Number of atoms          :  192 ( 647 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r1_filter_1 > v2_struct_0 > v1_relat_1 > v10_lattices > l3_lattices > #nlpp > k8_filter_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_filter_1,type,(
    r1_filter_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k8_filter_1,type,(
    k8_filter_1: $i > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v10_lattices(B)
              & l3_lattices(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & v10_lattices(C)
                  & l3_lattices(C) )
               => ( ( r1_filter_1(A,B)
                    & r1_filter_1(B,C) )
                 => r1_filter_1(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_filter_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => v1_relat_1(k8_filter_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_filter_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v10_lattices(B)
            & l3_lattices(B) )
         => ( r1_filter_1(A,B)
          <=> r4_wellord1(k8_filter_1(A),k8_filter_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_filter_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( ( r4_wellord1(A,B)
                  & r4_wellord1(B,C) )
               => r4_wellord1(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_wellord1)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10,plain,(
    ~ r1_filter_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_28,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_14,plain,(
    r1_filter_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8,plain,(
    ! [A_11] :
      ( v1_relat_1(k8_filter_1(A_11))
      | ~ l3_lattices(A_11)
      | ~ v10_lattices(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_18,plain,(
    v10_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_16,plain,(
    l3_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_22,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_12,plain,(
    r1_filter_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6,plain,(
    ! [A_8,B_10] :
      ( r4_wellord1(k8_filter_1(A_8),k8_filter_1(B_10))
      | ~ r1_filter_1(A_8,B_10)
      | ~ l3_lattices(B_10)
      | ~ v10_lattices(B_10)
      | v2_struct_0(B_10)
      | ~ l3_lattices(A_8)
      | ~ v10_lattices(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    ! [A_22,B_23] :
      ( r4_wellord1(k8_filter_1(A_22),k8_filter_1(B_23))
      | ~ r1_filter_1(A_22,B_23)
      | ~ l3_lattices(B_23)
      | ~ v10_lattices(B_23)
      | v2_struct_0(B_23)
      | ~ l3_lattices(A_22)
      | ~ v10_lattices(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1,C_7,B_5] :
      ( r4_wellord1(A_1,C_7)
      | ~ r4_wellord1(B_5,C_7)
      | ~ r4_wellord1(A_1,B_5)
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    ! [A_24,B_25,A_26] :
      ( r4_wellord1(A_24,k8_filter_1(B_25))
      | ~ r4_wellord1(A_24,k8_filter_1(A_26))
      | ~ v1_relat_1(k8_filter_1(B_25))
      | ~ v1_relat_1(k8_filter_1(A_26))
      | ~ v1_relat_1(A_24)
      | ~ r1_filter_1(A_26,B_25)
      | ~ l3_lattices(B_25)
      | ~ v10_lattices(B_25)
      | v2_struct_0(B_25)
      | ~ l3_lattices(A_26)
      | ~ v10_lattices(A_26)
      | v2_struct_0(A_26) ) ),
    inference(resolution,[status(thm)],[c_36,c_2])).

tff(c_48,plain,(
    ! [A_27,B_28,B_29] :
      ( r4_wellord1(k8_filter_1(A_27),k8_filter_1(B_28))
      | ~ v1_relat_1(k8_filter_1(B_28))
      | ~ v1_relat_1(k8_filter_1(B_29))
      | ~ v1_relat_1(k8_filter_1(A_27))
      | ~ r1_filter_1(B_29,B_28)
      | ~ l3_lattices(B_28)
      | ~ v10_lattices(B_28)
      | v2_struct_0(B_28)
      | ~ r1_filter_1(A_27,B_29)
      | ~ l3_lattices(B_29)
      | ~ v10_lattices(B_29)
      | v2_struct_0(B_29)
      | ~ l3_lattices(A_27)
      | ~ v10_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_6,c_44])).

tff(c_52,plain,(
    ! [A_30,B_31,A_32] :
      ( r4_wellord1(k8_filter_1(A_30),k8_filter_1(B_31))
      | ~ v1_relat_1(k8_filter_1(B_31))
      | ~ v1_relat_1(k8_filter_1(A_30))
      | ~ r1_filter_1(A_32,B_31)
      | ~ l3_lattices(B_31)
      | ~ v10_lattices(B_31)
      | v2_struct_0(B_31)
      | ~ r1_filter_1(A_30,A_32)
      | ~ l3_lattices(A_30)
      | ~ v10_lattices(A_30)
      | v2_struct_0(A_30)
      | ~ l3_lattices(A_32)
      | ~ v10_lattices(A_32)
      | v2_struct_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_8,c_48])).

tff(c_56,plain,(
    ! [A_30] :
      ( r4_wellord1(k8_filter_1(A_30),k8_filter_1('#skF_3'))
      | ~ v1_relat_1(k8_filter_1('#skF_3'))
      | ~ v1_relat_1(k8_filter_1(A_30))
      | ~ l3_lattices('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_filter_1(A_30,'#skF_2')
      | ~ l3_lattices(A_30)
      | ~ v10_lattices(A_30)
      | v2_struct_0(A_30)
      | ~ l3_lattices('#skF_2')
      | ~ v10_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12,c_52])).

tff(c_63,plain,(
    ! [A_30] :
      ( r4_wellord1(k8_filter_1(A_30),k8_filter_1('#skF_3'))
      | ~ v1_relat_1(k8_filter_1('#skF_3'))
      | ~ v1_relat_1(k8_filter_1(A_30))
      | v2_struct_0('#skF_3')
      | ~ r1_filter_1(A_30,'#skF_2')
      | ~ l3_lattices(A_30)
      | ~ v10_lattices(A_30)
      | v2_struct_0(A_30)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_18,c_16,c_56])).

tff(c_64,plain,(
    ! [A_30] :
      ( r4_wellord1(k8_filter_1(A_30),k8_filter_1('#skF_3'))
      | ~ v1_relat_1(k8_filter_1('#skF_3'))
      | ~ v1_relat_1(k8_filter_1(A_30))
      | ~ r1_filter_1(A_30,'#skF_2')
      | ~ l3_lattices(A_30)
      | ~ v10_lattices(A_30)
      | v2_struct_0(A_30) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_20,c_63])).

tff(c_108,plain,(
    ~ v1_relat_1(k8_filter_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_111,plain,
    ( ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_108])).

tff(c_114,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_111])).

tff(c_116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_114])).

tff(c_134,plain,(
    ! [A_36] :
      ( r4_wellord1(k8_filter_1(A_36),k8_filter_1('#skF_3'))
      | ~ v1_relat_1(k8_filter_1(A_36))
      | ~ r1_filter_1(A_36,'#skF_2')
      | ~ l3_lattices(A_36)
      | ~ v10_lattices(A_36)
      | v2_struct_0(A_36) ) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_4,plain,(
    ! [A_8,B_10] :
      ( r1_filter_1(A_8,B_10)
      | ~ r4_wellord1(k8_filter_1(A_8),k8_filter_1(B_10))
      | ~ l3_lattices(B_10)
      | ~ v10_lattices(B_10)
      | v2_struct_0(B_10)
      | ~ l3_lattices(A_8)
      | ~ v10_lattices(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_139,plain,(
    ! [A_36] :
      ( r1_filter_1(A_36,'#skF_3')
      | ~ l3_lattices('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v1_relat_1(k8_filter_1(A_36))
      | ~ r1_filter_1(A_36,'#skF_2')
      | ~ l3_lattices(A_36)
      | ~ v10_lattices(A_36)
      | v2_struct_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_134,c_4])).

tff(c_148,plain,(
    ! [A_36] :
      ( r1_filter_1(A_36,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v1_relat_1(k8_filter_1(A_36))
      | ~ r1_filter_1(A_36,'#skF_2')
      | ~ l3_lattices(A_36)
      | ~ v10_lattices(A_36)
      | v2_struct_0(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_139])).

tff(c_153,plain,(
    ! [A_37] :
      ( r1_filter_1(A_37,'#skF_3')
      | ~ v1_relat_1(k8_filter_1(A_37))
      | ~ r1_filter_1(A_37,'#skF_2')
      | ~ l3_lattices(A_37)
      | ~ v10_lattices(A_37)
      | v2_struct_0(A_37) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_148])).

tff(c_196,plain,(
    ! [A_40] :
      ( r1_filter_1(A_40,'#skF_3')
      | ~ r1_filter_1(A_40,'#skF_2')
      | ~ l3_lattices(A_40)
      | ~ v10_lattices(A_40)
      | v2_struct_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_8,c_153])).

tff(c_202,plain,
    ( r1_filter_1('#skF_1','#skF_3')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_196])).

tff(c_206,plain,
    ( r1_filter_1('#skF_1','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_202])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_10,c_206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:41:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.30  
% 2.16/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.30  %$ r4_wellord1 > r1_filter_1 > v2_struct_0 > v1_relat_1 > v10_lattices > l3_lattices > #nlpp > k8_filter_1 > #skF_2 > #skF_3 > #skF_1
% 2.16/1.30  
% 2.16/1.30  %Foreground sorts:
% 2.16/1.30  
% 2.16/1.30  
% 2.16/1.30  %Background operators:
% 2.16/1.30  
% 2.16/1.30  
% 2.16/1.30  %Foreground operators:
% 2.16/1.30  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.16/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.16/1.30  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.30  tff(r1_filter_1, type, r1_filter_1: ($i * $i) > $o).
% 2.16/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.30  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.30  tff(k8_filter_1, type, k8_filter_1: $i > $i).
% 2.16/1.30  
% 2.16/1.32  tff(f_97, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (((~v2_struct_0(B) & v10_lattices(B)) & l3_lattices(B)) => (![C]: (((~v2_struct_0(C) & v10_lattices(C)) & l3_lattices(C)) => ((r1_filter_1(A, B) & r1_filter_1(B, C)) => r1_filter_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_filter_1)).
% 2.16/1.32  tff(f_67, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => v1_relat_1(k8_filter_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_filter_1)).
% 2.16/1.32  tff(f_58, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (((~v2_struct_0(B) & v10_lattices(B)) & l3_lattices(B)) => (r1_filter_1(A, B) <=> r4_wellord1(k8_filter_1(A), k8_filter_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_filter_1)).
% 2.16/1.32  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((r4_wellord1(A, B) & r4_wellord1(B, C)) => r4_wellord1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_wellord1)).
% 2.16/1.32  tff(c_32, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.16/1.32  tff(c_10, plain, (~r1_filter_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.16/1.32  tff(c_30, plain, (v10_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.16/1.32  tff(c_28, plain, (l3_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.16/1.32  tff(c_14, plain, (r1_filter_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.16/1.32  tff(c_8, plain, (![A_11]: (v1_relat_1(k8_filter_1(A_11)) | ~l3_lattices(A_11) | ~v10_lattices(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.16/1.32  tff(c_20, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.16/1.32  tff(c_18, plain, (v10_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.16/1.32  tff(c_16, plain, (l3_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.16/1.32  tff(c_26, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.16/1.32  tff(c_24, plain, (v10_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.16/1.32  tff(c_22, plain, (l3_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.16/1.32  tff(c_12, plain, (r1_filter_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.16/1.32  tff(c_6, plain, (![A_8, B_10]: (r4_wellord1(k8_filter_1(A_8), k8_filter_1(B_10)) | ~r1_filter_1(A_8, B_10) | ~l3_lattices(B_10) | ~v10_lattices(B_10) | v2_struct_0(B_10) | ~l3_lattices(A_8) | ~v10_lattices(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.16/1.32  tff(c_36, plain, (![A_22, B_23]: (r4_wellord1(k8_filter_1(A_22), k8_filter_1(B_23)) | ~r1_filter_1(A_22, B_23) | ~l3_lattices(B_23) | ~v10_lattices(B_23) | v2_struct_0(B_23) | ~l3_lattices(A_22) | ~v10_lattices(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.16/1.32  tff(c_2, plain, (![A_1, C_7, B_5]: (r4_wellord1(A_1, C_7) | ~r4_wellord1(B_5, C_7) | ~r4_wellord1(A_1, B_5) | ~v1_relat_1(C_7) | ~v1_relat_1(B_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.16/1.32  tff(c_44, plain, (![A_24, B_25, A_26]: (r4_wellord1(A_24, k8_filter_1(B_25)) | ~r4_wellord1(A_24, k8_filter_1(A_26)) | ~v1_relat_1(k8_filter_1(B_25)) | ~v1_relat_1(k8_filter_1(A_26)) | ~v1_relat_1(A_24) | ~r1_filter_1(A_26, B_25) | ~l3_lattices(B_25) | ~v10_lattices(B_25) | v2_struct_0(B_25) | ~l3_lattices(A_26) | ~v10_lattices(A_26) | v2_struct_0(A_26))), inference(resolution, [status(thm)], [c_36, c_2])).
% 2.16/1.32  tff(c_48, plain, (![A_27, B_28, B_29]: (r4_wellord1(k8_filter_1(A_27), k8_filter_1(B_28)) | ~v1_relat_1(k8_filter_1(B_28)) | ~v1_relat_1(k8_filter_1(B_29)) | ~v1_relat_1(k8_filter_1(A_27)) | ~r1_filter_1(B_29, B_28) | ~l3_lattices(B_28) | ~v10_lattices(B_28) | v2_struct_0(B_28) | ~r1_filter_1(A_27, B_29) | ~l3_lattices(B_29) | ~v10_lattices(B_29) | v2_struct_0(B_29) | ~l3_lattices(A_27) | ~v10_lattices(A_27) | v2_struct_0(A_27))), inference(resolution, [status(thm)], [c_6, c_44])).
% 2.16/1.32  tff(c_52, plain, (![A_30, B_31, A_32]: (r4_wellord1(k8_filter_1(A_30), k8_filter_1(B_31)) | ~v1_relat_1(k8_filter_1(B_31)) | ~v1_relat_1(k8_filter_1(A_30)) | ~r1_filter_1(A_32, B_31) | ~l3_lattices(B_31) | ~v10_lattices(B_31) | v2_struct_0(B_31) | ~r1_filter_1(A_30, A_32) | ~l3_lattices(A_30) | ~v10_lattices(A_30) | v2_struct_0(A_30) | ~l3_lattices(A_32) | ~v10_lattices(A_32) | v2_struct_0(A_32))), inference(resolution, [status(thm)], [c_8, c_48])).
% 2.16/1.32  tff(c_56, plain, (![A_30]: (r4_wellord1(k8_filter_1(A_30), k8_filter_1('#skF_3')) | ~v1_relat_1(k8_filter_1('#skF_3')) | ~v1_relat_1(k8_filter_1(A_30)) | ~l3_lattices('#skF_3') | ~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~r1_filter_1(A_30, '#skF_2') | ~l3_lattices(A_30) | ~v10_lattices(A_30) | v2_struct_0(A_30) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_52])).
% 2.16/1.32  tff(c_63, plain, (![A_30]: (r4_wellord1(k8_filter_1(A_30), k8_filter_1('#skF_3')) | ~v1_relat_1(k8_filter_1('#skF_3')) | ~v1_relat_1(k8_filter_1(A_30)) | v2_struct_0('#skF_3') | ~r1_filter_1(A_30, '#skF_2') | ~l3_lattices(A_30) | ~v10_lattices(A_30) | v2_struct_0(A_30) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_18, c_16, c_56])).
% 2.16/1.32  tff(c_64, plain, (![A_30]: (r4_wellord1(k8_filter_1(A_30), k8_filter_1('#skF_3')) | ~v1_relat_1(k8_filter_1('#skF_3')) | ~v1_relat_1(k8_filter_1(A_30)) | ~r1_filter_1(A_30, '#skF_2') | ~l3_lattices(A_30) | ~v10_lattices(A_30) | v2_struct_0(A_30))), inference(negUnitSimplification, [status(thm)], [c_26, c_20, c_63])).
% 2.16/1.32  tff(c_108, plain, (~v1_relat_1(k8_filter_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_64])).
% 2.16/1.32  tff(c_111, plain, (~l3_lattices('#skF_3') | ~v10_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_8, c_108])).
% 2.16/1.32  tff(c_114, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_111])).
% 2.16/1.32  tff(c_116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_114])).
% 2.16/1.32  tff(c_134, plain, (![A_36]: (r4_wellord1(k8_filter_1(A_36), k8_filter_1('#skF_3')) | ~v1_relat_1(k8_filter_1(A_36)) | ~r1_filter_1(A_36, '#skF_2') | ~l3_lattices(A_36) | ~v10_lattices(A_36) | v2_struct_0(A_36))), inference(splitRight, [status(thm)], [c_64])).
% 2.16/1.32  tff(c_4, plain, (![A_8, B_10]: (r1_filter_1(A_8, B_10) | ~r4_wellord1(k8_filter_1(A_8), k8_filter_1(B_10)) | ~l3_lattices(B_10) | ~v10_lattices(B_10) | v2_struct_0(B_10) | ~l3_lattices(A_8) | ~v10_lattices(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.16/1.32  tff(c_139, plain, (![A_36]: (r1_filter_1(A_36, '#skF_3') | ~l3_lattices('#skF_3') | ~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~v1_relat_1(k8_filter_1(A_36)) | ~r1_filter_1(A_36, '#skF_2') | ~l3_lattices(A_36) | ~v10_lattices(A_36) | v2_struct_0(A_36))), inference(resolution, [status(thm)], [c_134, c_4])).
% 2.16/1.32  tff(c_148, plain, (![A_36]: (r1_filter_1(A_36, '#skF_3') | v2_struct_0('#skF_3') | ~v1_relat_1(k8_filter_1(A_36)) | ~r1_filter_1(A_36, '#skF_2') | ~l3_lattices(A_36) | ~v10_lattices(A_36) | v2_struct_0(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_139])).
% 2.16/1.32  tff(c_153, plain, (![A_37]: (r1_filter_1(A_37, '#skF_3') | ~v1_relat_1(k8_filter_1(A_37)) | ~r1_filter_1(A_37, '#skF_2') | ~l3_lattices(A_37) | ~v10_lattices(A_37) | v2_struct_0(A_37))), inference(negUnitSimplification, [status(thm)], [c_20, c_148])).
% 2.16/1.32  tff(c_196, plain, (![A_40]: (r1_filter_1(A_40, '#skF_3') | ~r1_filter_1(A_40, '#skF_2') | ~l3_lattices(A_40) | ~v10_lattices(A_40) | v2_struct_0(A_40))), inference(resolution, [status(thm)], [c_8, c_153])).
% 2.16/1.32  tff(c_202, plain, (r1_filter_1('#skF_1', '#skF_3') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_14, c_196])).
% 2.16/1.32  tff(c_206, plain, (r1_filter_1('#skF_1', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_202])).
% 2.16/1.32  tff(c_208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_10, c_206])).
% 2.16/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.32  
% 2.16/1.32  Inference rules
% 2.16/1.32  ----------------------
% 2.16/1.32  #Ref     : 0
% 2.16/1.32  #Sup     : 27
% 2.16/1.32  #Fact    : 0
% 2.16/1.32  #Define  : 0
% 2.16/1.32  #Split   : 5
% 2.16/1.32  #Chain   : 0
% 2.16/1.32  #Close   : 0
% 2.16/1.32  
% 2.16/1.32  Ordering : KBO
% 2.16/1.32  
% 2.16/1.32  Simplification rules
% 2.16/1.32  ----------------------
% 2.16/1.32  #Subsume      : 5
% 2.16/1.32  #Demod        : 46
% 2.16/1.32  #Tautology    : 2
% 2.16/1.32  #SimpNegUnit  : 17
% 2.16/1.32  #BackRed      : 0
% 2.16/1.32  
% 2.16/1.32  #Partial instantiations: 0
% 2.16/1.32  #Strategies tried      : 1
% 2.16/1.32  
% 2.16/1.32  Timing (in seconds)
% 2.16/1.32  ----------------------
% 2.16/1.32  Preprocessing        : 0.29
% 2.16/1.32  Parsing              : 0.17
% 2.16/1.32  CNF conversion       : 0.02
% 2.16/1.32  Main loop            : 0.22
% 2.16/1.32  Inferencing          : 0.09
% 2.16/1.32  Reduction            : 0.06
% 2.16/1.32  Demodulation         : 0.04
% 2.16/1.32  BG Simplification    : 0.01
% 2.16/1.32  Subsumption          : 0.05
% 2.16/1.32  Abstraction          : 0.01
% 2.16/1.32  MUC search           : 0.00
% 2.16/1.32  Cooper               : 0.00
% 2.16/1.32  Total                : 0.54
% 2.16/1.32  Index Insertion      : 0.00
% 2.16/1.32  Index Deletion       : 0.00
% 2.16/1.32  Index Matching       : 0.00
% 2.16/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
