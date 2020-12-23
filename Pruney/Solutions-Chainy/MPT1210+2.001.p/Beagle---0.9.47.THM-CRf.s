%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:18 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 231 expanded)
%              Number of leaves         :   31 (  93 expanded)
%              Depth                    :   14
%              Number of atoms          :  196 ( 850 expanded)
%              Number of equality atoms :   12 (  26 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v14_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k1_lattices > #nlpp > u1_struct_0 > k6_lattices > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(k6_lattices,type,(
    k6_lattices: $i > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v14_lattices,type,(
    v14_lattices: $i > $o )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v14_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r3_lattices(A,B,k6_lattices(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattices)).

tff(f_94,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => m1_subset_1(k6_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_lattices)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ( v14_lattices(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( B = k6_lattices(A)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( k1_lattices(A,B,C) = B
                    & k1_lattices(A,C,B) = B ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattices)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k1_lattices(A,B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

tff(f_47,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v4_lattices(A)
          & v5_lattices(A)
          & v6_lattices(A)
          & v7_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_lattices(A,B,C)
      <=> r1_lattices(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_42,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_54,plain,(
    ! [A_26] :
      ( l2_lattices(A_26)
      | ~ l3_lattices(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_58,plain,(
    l2_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_54])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_28,plain,(
    ! [A_19] :
      ( m1_subset_1(k6_lattices(A_19),u1_struct_0(A_19))
      | ~ l2_lattices(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_44,plain,(
    v14_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_104,plain,(
    ! [A_43,C_44] :
      ( k1_lattices(A_43,C_44,k6_lattices(A_43)) = k6_lattices(A_43)
      | ~ m1_subset_1(C_44,u1_struct_0(A_43))
      | ~ m1_subset_1(k6_lattices(A_43),u1_struct_0(A_43))
      | ~ v14_lattices(A_43)
      | ~ l2_lattices(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_110,plain,
    ( k1_lattices('#skF_2','#skF_3',k6_lattices('#skF_2')) = k6_lattices('#skF_2')
    | ~ m1_subset_1(k6_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v14_lattices('#skF_2')
    | ~ l2_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_104])).

tff(c_115,plain,
    ( k1_lattices('#skF_2','#skF_3',k6_lattices('#skF_2')) = k6_lattices('#skF_2')
    | ~ m1_subset_1(k6_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_44,c_110])).

tff(c_116,plain,
    ( k1_lattices('#skF_2','#skF_3',k6_lattices('#skF_2')) = k6_lattices('#skF_2')
    | ~ m1_subset_1(k6_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_115])).

tff(c_117,plain,(
    ~ m1_subset_1(k6_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_120,plain,
    ( ~ l2_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_117])).

tff(c_123,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_120])).

tff(c_125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_123])).

tff(c_126,plain,(
    k1_lattices('#skF_2','#skF_3',k6_lattices('#skF_2')) = k6_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_68,plain,(
    ! [A_39,B_40,C_41] :
      ( r1_lattices(A_39,B_40,C_41)
      | k1_lattices(A_39,B_40,C_41) != C_41
      | ~ m1_subset_1(C_41,u1_struct_0(A_39))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l2_lattices(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_76,plain,(
    ! [A_19,B_40] :
      ( r1_lattices(A_19,B_40,k6_lattices(A_19))
      | k1_lattices(A_19,B_40,k6_lattices(A_19)) != k6_lattices(A_19)
      | ~ m1_subset_1(B_40,u1_struct_0(A_19))
      | ~ l2_lattices(A_19)
      | v2_struct_0(A_19) ) ),
    inference(resolution,[status(thm)],[c_28,c_68])).

tff(c_46,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_228,plain,(
    ! [A_56,B_57,C_58] :
      ( r3_lattices(A_56,B_57,C_58)
      | ~ r1_lattices(A_56,B_57,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_56))
      | ~ m1_subset_1(B_57,u1_struct_0(A_56))
      | ~ l3_lattices(A_56)
      | ~ v9_lattices(A_56)
      | ~ v8_lattices(A_56)
      | ~ v6_lattices(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_236,plain,(
    ! [B_57] :
      ( r3_lattices('#skF_2',B_57,'#skF_3')
      | ~ r1_lattices('#skF_2',B_57,'#skF_3')
      | ~ m1_subset_1(B_57,u1_struct_0('#skF_2'))
      | ~ l3_lattices('#skF_2')
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_228])).

tff(c_245,plain,(
    ! [B_57] :
      ( r3_lattices('#skF_2',B_57,'#skF_3')
      | ~ r1_lattices('#skF_2',B_57,'#skF_3')
      | ~ m1_subset_1(B_57,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_236])).

tff(c_246,plain,(
    ! [B_57] :
      ( r3_lattices('#skF_2',B_57,'#skF_3')
      | ~ r1_lattices('#skF_2',B_57,'#skF_3')
      | ~ m1_subset_1(B_57,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ v6_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_245])).

tff(c_247,plain,(
    ~ v6_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_250,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_247])).

tff(c_253,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_250])).

tff(c_255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_253])).

tff(c_257,plain,(
    v6_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_256,plain,(
    ! [B_57] :
      ( ~ v8_lattices('#skF_2')
      | ~ v9_lattices('#skF_2')
      | r3_lattices('#skF_2',B_57,'#skF_3')
      | ~ r1_lattices('#skF_2',B_57,'#skF_3')
      | ~ m1_subset_1(B_57,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_258,plain,(
    ~ v9_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_262,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_258])).

tff(c_265,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_262])).

tff(c_267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_265])).

tff(c_268,plain,(
    ! [B_57] :
      ( ~ v8_lattices('#skF_2')
      | r3_lattices('#skF_2',B_57,'#skF_3')
      | ~ r1_lattices('#skF_2',B_57,'#skF_3')
      | ~ m1_subset_1(B_57,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_270,plain,(
    ~ v8_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_268])).

tff(c_276,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_270])).

tff(c_279,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_276])).

tff(c_281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_279])).

tff(c_283,plain,(
    v8_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_269,plain,(
    v9_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_127,plain,(
    m1_subset_1(k6_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_230,plain,(
    ! [B_57] :
      ( r3_lattices('#skF_2',B_57,k6_lattices('#skF_2'))
      | ~ r1_lattices('#skF_2',B_57,k6_lattices('#skF_2'))
      | ~ m1_subset_1(B_57,u1_struct_0('#skF_2'))
      | ~ l3_lattices('#skF_2')
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_127,c_228])).

tff(c_239,plain,(
    ! [B_57] :
      ( r3_lattices('#skF_2',B_57,k6_lattices('#skF_2'))
      | ~ r1_lattices('#skF_2',B_57,k6_lattices('#skF_2'))
      | ~ m1_subset_1(B_57,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_230])).

tff(c_240,plain,(
    ! [B_57] :
      ( r3_lattices('#skF_2',B_57,k6_lattices('#skF_2'))
      | ~ r1_lattices('#skF_2',B_57,k6_lattices('#skF_2'))
      | ~ m1_subset_1(B_57,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ v6_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_239])).

tff(c_321,plain,(
    ! [B_65] :
      ( r3_lattices('#skF_2',B_65,k6_lattices('#skF_2'))
      | ~ r1_lattices('#skF_2',B_65,k6_lattices('#skF_2'))
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_283,c_269,c_240])).

tff(c_38,plain,(
    ~ r3_lattices('#skF_2','#skF_3',k6_lattices('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_326,plain,
    ( ~ r1_lattices('#skF_2','#skF_3',k6_lattices('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_321,c_38])).

tff(c_333,plain,(
    ~ r1_lattices('#skF_2','#skF_3',k6_lattices('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_326])).

tff(c_336,plain,
    ( k1_lattices('#skF_2','#skF_3',k6_lattices('#skF_2')) != k6_lattices('#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l2_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_333])).

tff(c_342,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_40,c_126,c_336])).

tff(c_344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_342])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:58:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.31  
% 2.46/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.31  %$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v14_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k1_lattices > #nlpp > u1_struct_0 > k6_lattices > #skF_2 > #skF_3 > #skF_1
% 2.46/1.31  
% 2.46/1.31  %Foreground sorts:
% 2.46/1.31  
% 2.46/1.31  
% 2.46/1.31  %Background operators:
% 2.46/1.31  
% 2.46/1.31  
% 2.46/1.31  %Foreground operators:
% 2.46/1.31  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.46/1.31  tff(k6_lattices, type, k6_lattices: $i > $i).
% 2.46/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.46/1.31  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.46/1.31  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 2.46/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.31  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 2.46/1.31  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.46/1.31  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.46/1.31  tff(v4_lattices, type, v4_lattices: $i > $o).
% 2.46/1.31  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.46/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.31  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.46/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.31  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.46/1.31  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.46/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.31  tff(v14_lattices, type, v14_lattices: $i > $o).
% 2.46/1.31  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.46/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.46/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.46/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.31  tff(v7_lattices, type, v7_lattices: $i > $o).
% 2.46/1.31  
% 2.46/1.33  tff(f_128, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v14_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r3_lattices(A, B, k6_lattices(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_lattices)).
% 2.46/1.33  tff(f_94, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.46/1.33  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => m1_subset_1(k6_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_lattices)).
% 2.46/1.33  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (v14_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k6_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k1_lattices(A, B, C) = B) & (k1_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattices)).
% 2.46/1.33  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 2.46/1.33  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 2.46/1.33  tff(f_113, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 2.46/1.33  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.46/1.33  tff(c_42, plain, (l3_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.46/1.33  tff(c_54, plain, (![A_26]: (l2_lattices(A_26) | ~l3_lattices(A_26))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.46/1.33  tff(c_58, plain, (l2_lattices('#skF_2')), inference(resolution, [status(thm)], [c_42, c_54])).
% 2.46/1.33  tff(c_40, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.46/1.33  tff(c_28, plain, (![A_19]: (m1_subset_1(k6_lattices(A_19), u1_struct_0(A_19)) | ~l2_lattices(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.46/1.33  tff(c_44, plain, (v14_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.46/1.33  tff(c_104, plain, (![A_43, C_44]: (k1_lattices(A_43, C_44, k6_lattices(A_43))=k6_lattices(A_43) | ~m1_subset_1(C_44, u1_struct_0(A_43)) | ~m1_subset_1(k6_lattices(A_43), u1_struct_0(A_43)) | ~v14_lattices(A_43) | ~l2_lattices(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.46/1.33  tff(c_110, plain, (k1_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2'))=k6_lattices('#skF_2') | ~m1_subset_1(k6_lattices('#skF_2'), u1_struct_0('#skF_2')) | ~v14_lattices('#skF_2') | ~l2_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_104])).
% 2.46/1.33  tff(c_115, plain, (k1_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2'))=k6_lattices('#skF_2') | ~m1_subset_1(k6_lattices('#skF_2'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_44, c_110])).
% 2.46/1.33  tff(c_116, plain, (k1_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2'))=k6_lattices('#skF_2') | ~m1_subset_1(k6_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_115])).
% 2.46/1.33  tff(c_117, plain, (~m1_subset_1(k6_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_116])).
% 2.46/1.33  tff(c_120, plain, (~l2_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_117])).
% 2.46/1.33  tff(c_123, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_120])).
% 2.46/1.33  tff(c_125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_123])).
% 2.46/1.33  tff(c_126, plain, (k1_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2'))=k6_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_116])).
% 2.46/1.33  tff(c_68, plain, (![A_39, B_40, C_41]: (r1_lattices(A_39, B_40, C_41) | k1_lattices(A_39, B_40, C_41)!=C_41 | ~m1_subset_1(C_41, u1_struct_0(A_39)) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l2_lattices(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.46/1.33  tff(c_76, plain, (![A_19, B_40]: (r1_lattices(A_19, B_40, k6_lattices(A_19)) | k1_lattices(A_19, B_40, k6_lattices(A_19))!=k6_lattices(A_19) | ~m1_subset_1(B_40, u1_struct_0(A_19)) | ~l2_lattices(A_19) | v2_struct_0(A_19))), inference(resolution, [status(thm)], [c_28, c_68])).
% 2.46/1.33  tff(c_46, plain, (v10_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.46/1.33  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.46/1.33  tff(c_228, plain, (![A_56, B_57, C_58]: (r3_lattices(A_56, B_57, C_58) | ~r1_lattices(A_56, B_57, C_58) | ~m1_subset_1(C_58, u1_struct_0(A_56)) | ~m1_subset_1(B_57, u1_struct_0(A_56)) | ~l3_lattices(A_56) | ~v9_lattices(A_56) | ~v8_lattices(A_56) | ~v6_lattices(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.46/1.33  tff(c_236, plain, (![B_57]: (r3_lattices('#skF_2', B_57, '#skF_3') | ~r1_lattices('#skF_2', B_57, '#skF_3') | ~m1_subset_1(B_57, u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_228])).
% 2.46/1.33  tff(c_245, plain, (![B_57]: (r3_lattices('#skF_2', B_57, '#skF_3') | ~r1_lattices('#skF_2', B_57, '#skF_3') | ~m1_subset_1(B_57, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_236])).
% 2.46/1.33  tff(c_246, plain, (![B_57]: (r3_lattices('#skF_2', B_57, '#skF_3') | ~r1_lattices('#skF_2', B_57, '#skF_3') | ~m1_subset_1(B_57, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_245])).
% 2.46/1.33  tff(c_247, plain, (~v6_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_246])).
% 2.46/1.33  tff(c_250, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_8, c_247])).
% 2.46/1.33  tff(c_253, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46, c_250])).
% 2.46/1.33  tff(c_255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_253])).
% 2.46/1.33  tff(c_257, plain, (v6_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_246])).
% 2.46/1.33  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.46/1.33  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.46/1.33  tff(c_256, plain, (![B_57]: (~v8_lattices('#skF_2') | ~v9_lattices('#skF_2') | r3_lattices('#skF_2', B_57, '#skF_3') | ~r1_lattices('#skF_2', B_57, '#skF_3') | ~m1_subset_1(B_57, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_246])).
% 2.46/1.33  tff(c_258, plain, (~v9_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_256])).
% 2.46/1.33  tff(c_262, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_2, c_258])).
% 2.46/1.33  tff(c_265, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46, c_262])).
% 2.46/1.33  tff(c_267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_265])).
% 2.46/1.33  tff(c_268, plain, (![B_57]: (~v8_lattices('#skF_2') | r3_lattices('#skF_2', B_57, '#skF_3') | ~r1_lattices('#skF_2', B_57, '#skF_3') | ~m1_subset_1(B_57, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_256])).
% 2.46/1.33  tff(c_270, plain, (~v8_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_268])).
% 2.46/1.33  tff(c_276, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_4, c_270])).
% 2.46/1.33  tff(c_279, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46, c_276])).
% 2.46/1.33  tff(c_281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_279])).
% 2.46/1.33  tff(c_283, plain, (v8_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_268])).
% 2.46/1.33  tff(c_269, plain, (v9_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_256])).
% 2.46/1.33  tff(c_127, plain, (m1_subset_1(k6_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_116])).
% 2.46/1.33  tff(c_230, plain, (![B_57]: (r3_lattices('#skF_2', B_57, k6_lattices('#skF_2')) | ~r1_lattices('#skF_2', B_57, k6_lattices('#skF_2')) | ~m1_subset_1(B_57, u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_127, c_228])).
% 2.46/1.33  tff(c_239, plain, (![B_57]: (r3_lattices('#skF_2', B_57, k6_lattices('#skF_2')) | ~r1_lattices('#skF_2', B_57, k6_lattices('#skF_2')) | ~m1_subset_1(B_57, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_230])).
% 2.46/1.33  tff(c_240, plain, (![B_57]: (r3_lattices('#skF_2', B_57, k6_lattices('#skF_2')) | ~r1_lattices('#skF_2', B_57, k6_lattices('#skF_2')) | ~m1_subset_1(B_57, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_239])).
% 2.46/1.33  tff(c_321, plain, (![B_65]: (r3_lattices('#skF_2', B_65, k6_lattices('#skF_2')) | ~r1_lattices('#skF_2', B_65, k6_lattices('#skF_2')) | ~m1_subset_1(B_65, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_283, c_269, c_240])).
% 2.46/1.33  tff(c_38, plain, (~r3_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.46/1.33  tff(c_326, plain, (~r1_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_321, c_38])).
% 2.46/1.33  tff(c_333, plain, (~r1_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_326])).
% 2.46/1.33  tff(c_336, plain, (k1_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2'))!=k6_lattices('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l2_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_333])).
% 2.46/1.33  tff(c_342, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_40, c_126, c_336])).
% 2.46/1.33  tff(c_344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_342])).
% 2.46/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.33  
% 2.46/1.33  Inference rules
% 2.46/1.33  ----------------------
% 2.46/1.33  #Ref     : 0
% 2.46/1.33  #Sup     : 50
% 2.46/1.33  #Fact    : 0
% 2.46/1.33  #Define  : 0
% 2.46/1.33  #Split   : 9
% 2.46/1.33  #Chain   : 0
% 2.46/1.33  #Close   : 0
% 2.46/1.33  
% 2.46/1.33  Ordering : KBO
% 2.46/1.33  
% 2.46/1.33  Simplification rules
% 2.46/1.33  ----------------------
% 2.46/1.33  #Subsume      : 4
% 2.46/1.33  #Demod        : 60
% 2.46/1.33  #Tautology    : 18
% 2.46/1.33  #SimpNegUnit  : 24
% 2.46/1.33  #BackRed      : 1
% 2.46/1.33  
% 2.46/1.33  #Partial instantiations: 0
% 2.46/1.33  #Strategies tried      : 1
% 2.46/1.33  
% 2.46/1.33  Timing (in seconds)
% 2.46/1.33  ----------------------
% 2.46/1.33  Preprocessing        : 0.31
% 2.46/1.33  Parsing              : 0.17
% 2.46/1.33  CNF conversion       : 0.02
% 2.46/1.33  Main loop            : 0.25
% 2.46/1.33  Inferencing          : 0.10
% 2.46/1.33  Reduction            : 0.07
% 2.46/1.33  Demodulation         : 0.05
% 2.46/1.34  BG Simplification    : 0.02
% 2.46/1.34  Subsumption          : 0.05
% 2.46/1.34  Abstraction          : 0.01
% 2.46/1.34  MUC search           : 0.00
% 2.46/1.34  Cooper               : 0.00
% 2.46/1.34  Total                : 0.59
% 2.46/1.34  Index Insertion      : 0.00
% 2.46/1.34  Index Deletion       : 0.00
% 2.46/1.34  Index Matching       : 0.00
% 2.46/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
