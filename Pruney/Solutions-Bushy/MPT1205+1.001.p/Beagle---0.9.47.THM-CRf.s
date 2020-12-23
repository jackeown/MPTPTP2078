%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1205+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:35 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 243 expanded)
%              Number of leaves         :   33 (  99 expanded)
%              Depth                    :   13
%              Number of atoms          :  172 ( 740 expanded)
%              Number of equality atoms :   32 ( 125 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k3_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(k3_lattices,type,(
    k3_lattices: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v13_lattices,type,(
    v13_lattices: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v13_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k3_lattices(A,k5_lattices(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_lattices)).

tff(f_46,axiom,(
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

tff(f_93,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_87,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => m1_subset_1(k5_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

tff(f_65,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v8_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k1_lattices(A,k2_lattices(A,B,C),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_44,plain,(
    l3_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_48,plain,(
    v10_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_51,plain,(
    ! [A_29] :
      ( l1_lattices(A_29)
      | ~ l3_lattices(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_55,plain,(
    l1_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_51])).

tff(c_32,plain,(
    ! [A_23] :
      ( m1_subset_1(k5_lattices(A_23),u1_struct_0(A_23))
      | ~ l1_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_46,plain,(
    v13_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_72,plain,(
    ! [A_43,C_44] :
      ( k2_lattices(A_43,C_44,k5_lattices(A_43)) = k5_lattices(A_43)
      | ~ m1_subset_1(C_44,u1_struct_0(A_43))
      | ~ m1_subset_1(k5_lattices(A_43),u1_struct_0(A_43))
      | ~ v13_lattices(A_43)
      | ~ l1_lattices(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_82,plain,
    ( k2_lattices('#skF_4','#skF_5',k5_lattices('#skF_4')) = k5_lattices('#skF_4')
    | ~ m1_subset_1(k5_lattices('#skF_4'),u1_struct_0('#skF_4'))
    | ~ v13_lattices('#skF_4')
    | ~ l1_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_72])).

tff(c_89,plain,
    ( k2_lattices('#skF_4','#skF_5',k5_lattices('#skF_4')) = k5_lattices('#skF_4')
    | ~ m1_subset_1(k5_lattices('#skF_4'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_46,c_82])).

tff(c_90,plain,
    ( k2_lattices('#skF_4','#skF_5',k5_lattices('#skF_4')) = k5_lattices('#skF_4')
    | ~ m1_subset_1(k5_lattices('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_89])).

tff(c_91,plain,(
    ~ m1_subset_1(k5_lattices('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_94,plain,
    ( ~ l1_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_91])).

tff(c_97,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_94])).

tff(c_99,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_97])).

tff(c_101,plain,(
    m1_subset_1(k5_lattices('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,(
    ! [A_30] :
      ( l2_lattices(A_30)
      | ~ l3_lattices(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_60,plain,(
    l2_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_56])).

tff(c_108,plain,(
    ! [A_45,B_46,C_47] :
      ( k3_lattices(A_45,B_46,C_47) = k1_lattices(A_45,B_46,C_47)
      | ~ m1_subset_1(C_47,u1_struct_0(A_45))
      | ~ m1_subset_1(B_46,u1_struct_0(A_45))
      | ~ l2_lattices(A_45)
      | ~ v4_lattices(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_120,plain,(
    ! [B_46] :
      ( k3_lattices('#skF_4',B_46,'#skF_5') = k1_lattices('#skF_4',B_46,'#skF_5')
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_4'))
      | ~ l2_lattices('#skF_4')
      | ~ v4_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_108])).

tff(c_131,plain,(
    ! [B_46] :
      ( k3_lattices('#skF_4',B_46,'#skF_5') = k1_lattices('#skF_4',B_46,'#skF_5')
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_4'))
      | ~ v4_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_120])).

tff(c_132,plain,(
    ! [B_46] :
      ( k3_lattices('#skF_4',B_46,'#skF_5') = k1_lattices('#skF_4',B_46,'#skF_5')
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_4'))
      | ~ v4_lattices('#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_131])).

tff(c_141,plain,(
    ~ v4_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_145,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_141])).

tff(c_148,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_145])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_148])).

tff(c_153,plain,(
    ! [B_48] :
      ( k3_lattices('#skF_4',B_48,'#skF_5') = k1_lattices('#skF_4',B_48,'#skF_5')
      | ~ m1_subset_1(B_48,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_176,plain,(
    k3_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5') = k1_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_101,c_153])).

tff(c_40,plain,(
    k3_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_198,plain,(
    k1_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_40])).

tff(c_283,plain,(
    ! [A_53,C_54] :
      ( k2_lattices(A_53,k5_lattices(A_53),C_54) = k5_lattices(A_53)
      | ~ m1_subset_1(C_54,u1_struct_0(A_53))
      | ~ m1_subset_1(k5_lattices(A_53),u1_struct_0(A_53))
      | ~ v13_lattices(A_53)
      | ~ l1_lattices(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_295,plain,
    ( k2_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5') = k5_lattices('#skF_4')
    | ~ m1_subset_1(k5_lattices('#skF_4'),u1_struct_0('#skF_4'))
    | ~ v13_lattices('#skF_4')
    | ~ l1_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_283])).

tff(c_306,plain,
    ( k2_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5') = k5_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_46,c_101,c_295])).

tff(c_307,plain,(
    k2_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5') = k5_lattices('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_306])).

tff(c_28,plain,(
    ! [A_12] :
      ( m1_subset_1('#skF_3'(A_12),u1_struct_0(A_12))
      | v8_lattices(A_12)
      | ~ l3_lattices(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_164,plain,
    ( k3_lattices('#skF_4','#skF_3'('#skF_4'),'#skF_5') = k1_lattices('#skF_4','#skF_3'('#skF_4'),'#skF_5')
    | v8_lattices('#skF_4')
    | ~ l3_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_153])).

tff(c_183,plain,
    ( k3_lattices('#skF_4','#skF_3'('#skF_4'),'#skF_5') = k1_lattices('#skF_4','#skF_3'('#skF_4'),'#skF_5')
    | v8_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_164])).

tff(c_184,plain,
    ( k3_lattices('#skF_4','#skF_3'('#skF_4'),'#skF_5') = k1_lattices('#skF_4','#skF_3'('#skF_4'),'#skF_5')
    | v8_lattices('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_183])).

tff(c_229,plain,(
    v8_lattices('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_203,plain,(
    ! [A_49,B_50,C_51] :
      ( k1_lattices(A_49,k2_lattices(A_49,B_50,C_51),C_51) = C_51
      | ~ m1_subset_1(C_51,u1_struct_0(A_49))
      | ~ m1_subset_1(B_50,u1_struct_0(A_49))
      | ~ v8_lattices(A_49)
      | ~ l3_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_215,plain,(
    ! [B_50] :
      ( k1_lattices('#skF_4',k2_lattices('#skF_4',B_50,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_4'))
      | ~ v8_lattices('#skF_4')
      | ~ l3_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_203])).

tff(c_226,plain,(
    ! [B_50] :
      ( k1_lattices('#skF_4',k2_lattices('#skF_4',B_50,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_4'))
      | ~ v8_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_215])).

tff(c_227,plain,(
    ! [B_50] :
      ( k1_lattices('#skF_4',k2_lattices('#skF_4',B_50,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_4'))
      | ~ v8_lattices('#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_226])).

tff(c_234,plain,(
    ! [B_52] :
      ( k1_lattices('#skF_4',k2_lattices('#skF_4',B_52,'#skF_5'),'#skF_5') = '#skF_5'
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_227])).

tff(c_257,plain,(
    k1_lattices('#skF_4',k2_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5'),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_101,c_234])).

tff(c_308,plain,(
    k1_lattices('#skF_4',k5_lattices('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_257])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_308])).

tff(c_312,plain,(
    ~ v8_lattices('#skF_4') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_315,plain,
    ( ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l3_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_312])).

tff(c_318,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_315])).

tff(c_320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_318])).

%------------------------------------------------------------------------------
