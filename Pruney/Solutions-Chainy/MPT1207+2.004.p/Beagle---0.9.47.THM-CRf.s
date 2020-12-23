%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:16 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 256 expanded)
%              Number of leaves         :   31 ( 101 expanded)
%              Depth                    :   12
%              Number of atoms          :  183 ( 926 expanded)
%              Number of equality atoms :   16 (  70 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(v13_lattices,type,(
    v13_lattices: $i > $o )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_lattices,type,(
    k5_lattices: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v13_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r3_lattices(A,k5_lattices(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattices)).

tff(f_79,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => m1_subset_1(k5_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => ( v13_lattices(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( B = k5_lattices(A)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( k2_lattices(A,B,C) = B
                    & k2_lattices(A,C,B) = B ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_117,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k2_lattices(A,B,C) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

tff(f_98,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

tff(c_38,plain,(
    ~ r3_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_42,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_49,plain,(
    ! [A_25] :
      ( l1_lattices(A_25)
      | ~ l3_lattices(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_53,plain,(
    l1_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_49])).

tff(c_24,plain,(
    ! [A_12] :
      ( m1_subset_1(k5_lattices(A_12),u1_struct_0(A_12))
      | ~ l1_lattices(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,(
    v13_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_67,plain,(
    ! [A_36,C_37] :
      ( k2_lattices(A_36,k5_lattices(A_36),C_37) = k5_lattices(A_36)
      | ~ m1_subset_1(C_37,u1_struct_0(A_36))
      | ~ m1_subset_1(k5_lattices(A_36),u1_struct_0(A_36))
      | ~ v13_lattices(A_36)
      | ~ l1_lattices(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_73,plain,
    ( k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v13_lattices('#skF_2')
    | ~ l1_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_67])).

tff(c_78,plain,
    ( k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_44,c_73])).

tff(c_79,plain,
    ( k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_78])).

tff(c_80,plain,(
    ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_83,plain,
    ( ~ l1_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_80])).

tff(c_86,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_83])).

tff(c_88,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_86])).

tff(c_89,plain,(
    k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_90,plain,(
    m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_46,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_162,plain,(
    ! [A_45,B_46,C_47] :
      ( r1_lattices(A_45,B_46,C_47)
      | k2_lattices(A_45,B_46,C_47) != B_46
      | ~ m1_subset_1(C_47,u1_struct_0(A_45))
      | ~ m1_subset_1(B_46,u1_struct_0(A_45))
      | ~ l3_lattices(A_45)
      | ~ v9_lattices(A_45)
      | ~ v8_lattices(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_170,plain,(
    ! [B_46] :
      ( r1_lattices('#skF_2',B_46,'#skF_3')
      | k2_lattices('#skF_2',B_46,'#skF_3') != B_46
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2'))
      | ~ l3_lattices('#skF_2')
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_162])).

tff(c_179,plain,(
    ! [B_46] :
      ( r1_lattices('#skF_2',B_46,'#skF_3')
      | k2_lattices('#skF_2',B_46,'#skF_3') != B_46
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_170])).

tff(c_180,plain,(
    ! [B_46] :
      ( r1_lattices('#skF_2',B_46,'#skF_3')
      | k2_lattices('#skF_2',B_46,'#skF_3') != B_46
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_179])).

tff(c_181,plain,(
    ~ v8_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_184,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_181])).

tff(c_187,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_184])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_187])).

tff(c_190,plain,(
    ! [B_46] :
      ( ~ v9_lattices('#skF_2')
      | r1_lattices('#skF_2',B_46,'#skF_3')
      | k2_lattices('#skF_2',B_46,'#skF_3') != B_46
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_192,plain,(
    ~ v9_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_195,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_192])).

tff(c_198,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_195])).

tff(c_200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_198])).

tff(c_204,plain,(
    ! [B_51] :
      ( r1_lattices('#skF_2',B_51,'#skF_3')
      | k2_lattices('#skF_2',B_51,'#skF_3') != B_51
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_207,plain,
    ( r1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3')
    | k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') != k5_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_204])).

tff(c_221,plain,(
    r1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_207])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_191,plain,(
    v8_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_202,plain,(
    v9_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_259,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_267,plain,(
    ! [B_57] :
      ( r3_lattices('#skF_2',B_57,'#skF_3')
      | ~ r1_lattices('#skF_2',B_57,'#skF_3')
      | ~ m1_subset_1(B_57,u1_struct_0('#skF_2'))
      | ~ l3_lattices('#skF_2')
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_259])).

tff(c_276,plain,(
    ! [B_57] :
      ( r3_lattices('#skF_2',B_57,'#skF_3')
      | ~ r1_lattices('#skF_2',B_57,'#skF_3')
      | ~ m1_subset_1(B_57,u1_struct_0('#skF_2'))
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_202,c_42,c_267])).

tff(c_277,plain,(
    ! [B_57] :
      ( r3_lattices('#skF_2',B_57,'#skF_3')
      | ~ r1_lattices('#skF_2',B_57,'#skF_3')
      | ~ m1_subset_1(B_57,u1_struct_0('#skF_2'))
      | ~ v6_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_276])).

tff(c_278,plain,(
    ~ v6_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_277])).

tff(c_281,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_278])).

tff(c_284,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_281])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_284])).

tff(c_298,plain,(
    ! [B_60] :
      ( r3_lattices('#skF_2',B_60,'#skF_3')
      | ~ r1_lattices('#skF_2',B_60,'#skF_3')
      | ~ m1_subset_1(B_60,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_277])).

tff(c_301,plain,
    ( r3_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3')
    | ~ r1_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_298])).

tff(c_315,plain,(
    r3_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_301])).

tff(c_317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_315])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.39  
% 2.61/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.39  %$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_3 > #skF_1
% 2.61/1.39  
% 2.61/1.39  %Foreground sorts:
% 2.61/1.39  
% 2.61/1.39  
% 2.61/1.39  %Background operators:
% 2.61/1.39  
% 2.61/1.39  
% 2.61/1.39  %Foreground operators:
% 2.61/1.39  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.61/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.61/1.39  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 2.61/1.39  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.61/1.39  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 2.61/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.39  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.61/1.39  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.61/1.39  tff(v4_lattices, type, v4_lattices: $i > $o).
% 2.61/1.39  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.61/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.39  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.61/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.39  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.61/1.39  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.61/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.39  tff(v13_lattices, type, v13_lattices: $i > $o).
% 2.61/1.39  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.61/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.39  tff(k5_lattices, type, k5_lattices: $i > $i).
% 2.61/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.61/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.61/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.39  tff(v7_lattices, type, v7_lattices: $i > $o).
% 2.61/1.39  
% 2.61/1.41  tff(f_132, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r3_lattices(A, k5_lattices(A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_lattices)).
% 2.61/1.41  tff(f_79, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.61/1.41  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 2.61/1.41  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k5_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 2.61/1.41  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 2.61/1.41  tff(f_117, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 2.61/1.41  tff(f_98, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 2.61/1.41  tff(c_38, plain, (~r3_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.61/1.41  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.61/1.41  tff(c_42, plain, (l3_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.61/1.41  tff(c_49, plain, (![A_25]: (l1_lattices(A_25) | ~l3_lattices(A_25))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.61/1.41  tff(c_53, plain, (l1_lattices('#skF_2')), inference(resolution, [status(thm)], [c_42, c_49])).
% 2.61/1.41  tff(c_24, plain, (![A_12]: (m1_subset_1(k5_lattices(A_12), u1_struct_0(A_12)) | ~l1_lattices(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.61/1.41  tff(c_44, plain, (v13_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.61/1.41  tff(c_40, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.61/1.41  tff(c_67, plain, (![A_36, C_37]: (k2_lattices(A_36, k5_lattices(A_36), C_37)=k5_lattices(A_36) | ~m1_subset_1(C_37, u1_struct_0(A_36)) | ~m1_subset_1(k5_lattices(A_36), u1_struct_0(A_36)) | ~v13_lattices(A_36) | ~l1_lattices(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.61/1.41  tff(c_73, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | ~v13_lattices('#skF_2') | ~l1_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_67])).
% 2.61/1.41  tff(c_78, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_44, c_73])).
% 2.61/1.41  tff(c_79, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_78])).
% 2.61/1.41  tff(c_80, plain, (~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_79])).
% 2.61/1.41  tff(c_83, plain, (~l1_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_80])).
% 2.61/1.41  tff(c_86, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_83])).
% 2.61/1.41  tff(c_88, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_86])).
% 2.61/1.41  tff(c_89, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_79])).
% 2.61/1.41  tff(c_90, plain, (m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_79])).
% 2.61/1.41  tff(c_46, plain, (v10_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.61/1.41  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.61/1.41  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.61/1.41  tff(c_162, plain, (![A_45, B_46, C_47]: (r1_lattices(A_45, B_46, C_47) | k2_lattices(A_45, B_46, C_47)!=B_46 | ~m1_subset_1(C_47, u1_struct_0(A_45)) | ~m1_subset_1(B_46, u1_struct_0(A_45)) | ~l3_lattices(A_45) | ~v9_lattices(A_45) | ~v8_lattices(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.61/1.41  tff(c_170, plain, (![B_46]: (r1_lattices('#skF_2', B_46, '#skF_3') | k2_lattices('#skF_2', B_46, '#skF_3')!=B_46 | ~m1_subset_1(B_46, u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_162])).
% 2.61/1.41  tff(c_179, plain, (![B_46]: (r1_lattices('#skF_2', B_46, '#skF_3') | k2_lattices('#skF_2', B_46, '#skF_3')!=B_46 | ~m1_subset_1(B_46, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_170])).
% 2.61/1.41  tff(c_180, plain, (![B_46]: (r1_lattices('#skF_2', B_46, '#skF_3') | k2_lattices('#skF_2', B_46, '#skF_3')!=B_46 | ~m1_subset_1(B_46, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_179])).
% 2.61/1.41  tff(c_181, plain, (~v8_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_180])).
% 2.61/1.41  tff(c_184, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_4, c_181])).
% 2.61/1.41  tff(c_187, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46, c_184])).
% 2.61/1.41  tff(c_189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_187])).
% 2.61/1.41  tff(c_190, plain, (![B_46]: (~v9_lattices('#skF_2') | r1_lattices('#skF_2', B_46, '#skF_3') | k2_lattices('#skF_2', B_46, '#skF_3')!=B_46 | ~m1_subset_1(B_46, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_180])).
% 2.61/1.41  tff(c_192, plain, (~v9_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_190])).
% 2.61/1.41  tff(c_195, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_2, c_192])).
% 2.61/1.41  tff(c_198, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46, c_195])).
% 2.61/1.41  tff(c_200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_198])).
% 2.61/1.41  tff(c_204, plain, (![B_51]: (r1_lattices('#skF_2', B_51, '#skF_3') | k2_lattices('#skF_2', B_51, '#skF_3')!=B_51 | ~m1_subset_1(B_51, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_190])).
% 2.61/1.41  tff(c_207, plain, (r1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3') | k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')!=k5_lattices('#skF_2')), inference(resolution, [status(thm)], [c_90, c_204])).
% 2.61/1.41  tff(c_221, plain, (r1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_207])).
% 2.61/1.41  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.61/1.41  tff(c_191, plain, (v8_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_180])).
% 2.61/1.41  tff(c_202, plain, (v9_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_190])).
% 2.61/1.41  tff(c_259, plain, (![A_56, B_57, C_58]: (r3_lattices(A_56, B_57, C_58) | ~r1_lattices(A_56, B_57, C_58) | ~m1_subset_1(C_58, u1_struct_0(A_56)) | ~m1_subset_1(B_57, u1_struct_0(A_56)) | ~l3_lattices(A_56) | ~v9_lattices(A_56) | ~v8_lattices(A_56) | ~v6_lattices(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.61/1.41  tff(c_267, plain, (![B_57]: (r3_lattices('#skF_2', B_57, '#skF_3') | ~r1_lattices('#skF_2', B_57, '#skF_3') | ~m1_subset_1(B_57, u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_259])).
% 2.61/1.41  tff(c_276, plain, (![B_57]: (r3_lattices('#skF_2', B_57, '#skF_3') | ~r1_lattices('#skF_2', B_57, '#skF_3') | ~m1_subset_1(B_57, u1_struct_0('#skF_2')) | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_202, c_42, c_267])).
% 2.61/1.41  tff(c_277, plain, (![B_57]: (r3_lattices('#skF_2', B_57, '#skF_3') | ~r1_lattices('#skF_2', B_57, '#skF_3') | ~m1_subset_1(B_57, u1_struct_0('#skF_2')) | ~v6_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_276])).
% 2.61/1.41  tff(c_278, plain, (~v6_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_277])).
% 2.61/1.41  tff(c_281, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_8, c_278])).
% 2.61/1.41  tff(c_284, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46, c_281])).
% 2.61/1.41  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_284])).
% 2.61/1.41  tff(c_298, plain, (![B_60]: (r3_lattices('#skF_2', B_60, '#skF_3') | ~r1_lattices('#skF_2', B_60, '#skF_3') | ~m1_subset_1(B_60, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_277])).
% 2.61/1.41  tff(c_301, plain, (r3_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3') | ~r1_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_90, c_298])).
% 2.61/1.41  tff(c_315, plain, (r3_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_301])).
% 2.61/1.41  tff(c_317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_315])).
% 2.61/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.41  
% 2.61/1.41  Inference rules
% 2.61/1.41  ----------------------
% 2.61/1.41  #Ref     : 0
% 2.61/1.41  #Sup     : 47
% 2.61/1.41  #Fact    : 0
% 2.61/1.41  #Define  : 0
% 2.61/1.41  #Split   : 5
% 2.61/1.41  #Chain   : 0
% 2.61/1.41  #Close   : 0
% 2.61/1.41  
% 2.61/1.41  Ordering : KBO
% 2.61/1.41  
% 2.61/1.41  Simplification rules
% 2.61/1.41  ----------------------
% 2.61/1.41  #Subsume      : 2
% 2.61/1.41  #Demod        : 63
% 2.61/1.41  #Tautology    : 19
% 2.61/1.41  #SimpNegUnit  : 22
% 2.61/1.41  #BackRed      : 0
% 2.61/1.41  
% 2.61/1.41  #Partial instantiations: 0
% 2.61/1.41  #Strategies tried      : 1
% 2.61/1.41  
% 2.61/1.41  Timing (in seconds)
% 2.61/1.41  ----------------------
% 2.61/1.41  Preprocessing        : 0.33
% 2.61/1.41  Parsing              : 0.18
% 2.61/1.41  CNF conversion       : 0.02
% 2.61/1.41  Main loop            : 0.27
% 2.61/1.41  Inferencing          : 0.10
% 2.61/1.41  Reduction            : 0.08
% 2.61/1.41  Demodulation         : 0.05
% 2.61/1.41  BG Simplification    : 0.02
% 2.61/1.41  Subsumption          : 0.05
% 2.61/1.41  Abstraction          : 0.01
% 2.61/1.41  MUC search           : 0.00
% 2.61/1.41  Cooper               : 0.00
% 2.61/1.41  Total                : 0.64
% 2.61/1.41  Index Insertion      : 0.00
% 2.61/1.41  Index Deletion       : 0.00
% 2.61/1.41  Index Matching       : 0.00
% 2.61/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
