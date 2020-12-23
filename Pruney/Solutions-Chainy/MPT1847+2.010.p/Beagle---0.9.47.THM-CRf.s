%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:53 EST 2020

% Result     : Theorem 4.82s
% Output     : CNFRefutation 5.08s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 477 expanded)
%              Number of leaves         :   25 ( 178 expanded)
%              Depth                    :   20
%              Number of atoms          :  177 (1448 expanded)
%              Number of equality atoms :   16 ( 205 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( ( g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
                    & v1_tex_2(B,A) )
                 => v1_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tex_2)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_28,plain,(
    ~ v1_tex_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_30,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_26,plain,(
    ! [A_16,B_22] :
      ( m1_subset_1('#skF_1'(A_16,B_22),k1_zfmisc_1(u1_struct_0(A_16)))
      | v1_tex_2(B_22,A_16)
      | ~ m1_pre_topc(B_22,A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_42,plain,(
    ! [B_32,A_33] :
      ( l1_pre_topc(B_32)
      | ~ m1_pre_topc(B_32,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_48,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_42])).

tff(c_55,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_48])).

tff(c_16,plain,(
    ! [A_12] :
      ( m1_pre_topc(A_12,A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_91,plain,(
    ! [B_41,A_42] :
      ( u1_struct_0(B_41) = '#skF_1'(A_42,B_41)
      | v1_tex_2(B_41,A_42)
      | ~ m1_pre_topc(B_41,A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_94,plain,
    ( u1_struct_0('#skF_4') = '#skF_1'('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_91,c_28])).

tff(c_97,plain,(
    u1_struct_0('#skF_4') = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_94])).

tff(c_157,plain,(
    ! [A_47,B_48] :
      ( m1_pre_topc(A_47,g1_pre_topc(u1_struct_0(B_48),u1_pre_topc(B_48)))
      | ~ m1_pre_topc(A_47,B_48)
      | ~ l1_pre_topc(B_48)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_169,plain,(
    ! [A_47] :
      ( m1_pre_topc(A_47,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_47,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_157])).

tff(c_203,plain,(
    ! [A_51] :
      ( m1_pre_topc(A_51,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_51,'#skF_4')
      | ~ l1_pre_topc(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_169])).

tff(c_51,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_42])).

tff(c_58,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_51])).

tff(c_32,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_74,plain,(
    ! [B_38,A_39] :
      ( m1_pre_topc(B_38,A_39)
      | ~ m1_pre_topc(B_38,g1_pre_topc(u1_struct_0(A_39),u1_pre_topc(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_77,plain,(
    ! [B_38] :
      ( m1_pre_topc(B_38,'#skF_3')
      | ~ m1_pre_topc(B_38,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_74])).

tff(c_83,plain,(
    ! [B_38] :
      ( m1_pre_topc(B_38,'#skF_3')
      | ~ m1_pre_topc(B_38,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_77])).

tff(c_98,plain,(
    ! [B_38] :
      ( m1_pre_topc(B_38,'#skF_3')
      | ~ m1_pre_topc(B_38,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_83])).

tff(c_214,plain,(
    ! [A_51] :
      ( m1_pre_topc(A_51,'#skF_3')
      | ~ m1_pre_topc(A_51,'#skF_4')
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_203,c_98])).

tff(c_99,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_32])).

tff(c_166,plain,(
    ! [A_47] :
      ( m1_pre_topc(A_47,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_47,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_157])).

tff(c_176,plain,(
    ! [A_49] :
      ( m1_pre_topc(A_49,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_49,'#skF_3')
      | ~ l1_pre_topc(A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_166])).

tff(c_10,plain,(
    ! [B_8,A_6] :
      ( m1_pre_topc(B_8,A_6)
      | ~ m1_pre_topc(B_8,g1_pre_topc(u1_struct_0(A_6),u1_pre_topc(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_103,plain,(
    ! [B_8] :
      ( m1_pre_topc(B_8,'#skF_4')
      | ~ m1_pre_topc(B_8,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_10])).

tff(c_113,plain,(
    ! [B_8] :
      ( m1_pre_topc(B_8,'#skF_4')
      | ~ m1_pre_topc(B_8,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_103])).

tff(c_189,plain,(
    ! [A_50] :
      ( m1_pre_topc(A_50,'#skF_4')
      | ~ m1_pre_topc(A_50,'#skF_3')
      | ~ l1_pre_topc(A_50) ) ),
    inference(resolution,[status(thm)],[c_176,c_113])).

tff(c_193,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_189])).

tff(c_196,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_193])).

tff(c_18,plain,(
    ! [B_15,A_13] :
      ( r1_tarski(u1_struct_0(B_15),u1_struct_0(A_13))
      | ~ m1_pre_topc(B_15,A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_106,plain,(
    ! [A_13] :
      ( r1_tarski('#skF_1'('#skF_2','#skF_4'),u1_struct_0(A_13))
      | ~ m1_pre_topc('#skF_4',A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_18])).

tff(c_70,plain,(
    ! [B_36,A_37] :
      ( r1_tarski(u1_struct_0(B_36),u1_struct_0(A_37))
      | ~ m1_pre_topc(B_36,A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_234,plain,(
    ! [B_56,A_57] :
      ( u1_struct_0(B_56) = u1_struct_0(A_57)
      | ~ r1_tarski(u1_struct_0(A_57),u1_struct_0(B_56))
      | ~ m1_pre_topc(B_56,A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(resolution,[status(thm)],[c_70,c_2])).

tff(c_237,plain,(
    ! [B_56] :
      ( u1_struct_0(B_56) = u1_struct_0('#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_2','#skF_4'),u1_struct_0(B_56))
      | ~ m1_pre_topc(B_56,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_234])).

tff(c_254,plain,(
    ! [B_58] :
      ( u1_struct_0(B_58) = '#skF_1'('#skF_2','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_2','#skF_4'),u1_struct_0(B_58))
      | ~ m1_pre_topc(B_58,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_97,c_237])).

tff(c_270,plain,(
    ! [A_61] :
      ( u1_struct_0(A_61) = '#skF_1'('#skF_2','#skF_4')
      | ~ m1_pre_topc(A_61,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_106,c_254])).

tff(c_272,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_196,c_270])).

tff(c_278,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_272])).

tff(c_282,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_285,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_214,c_282])).

tff(c_288,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_285])).

tff(c_292,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_288])).

tff(c_296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_292])).

tff(c_297,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_392,plain,(
    ! [B_64,A_65] :
      ( v1_subset_1(u1_struct_0(B_64),u1_struct_0(A_65))
      | ~ m1_subset_1(u1_struct_0(B_64),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ v1_tex_2(B_64,A_65)
      | ~ m1_pre_topc(B_64,A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_395,plain,(
    ! [A_65] :
      ( v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0(A_65))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ v1_tex_2('#skF_3',A_65)
      | ~ m1_pre_topc('#skF_3',A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_392])).

tff(c_2349,plain,(
    ! [A_138] :
      ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),u1_struct_0(A_138))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ v1_tex_2('#skF_3',A_138)
      | ~ m1_pre_topc('#skF_3',A_138)
      | ~ l1_pre_topc(A_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_395])).

tff(c_2356,plain,
    ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v1_tex_2('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_2349])).

tff(c_2364,plain,
    ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | v1_tex_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_36,c_30,c_2356])).

tff(c_2365,plain,(
    v1_subset_1('#skF_1'('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2364])).

tff(c_22,plain,(
    ! [A_16,B_22] :
      ( ~ v1_subset_1('#skF_1'(A_16,B_22),u1_struct_0(A_16))
      | v1_tex_2(B_22,A_16)
      | ~ m1_pre_topc(B_22,A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2370,plain,
    ( v1_tex_2('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2365,c_22])).

tff(c_2373,plain,(
    v1_tex_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_2370])).

tff(c_2375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2373])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:25:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.82/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.08/1.92  
% 5.08/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.08/1.93  %$ v1_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.08/1.93  
% 5.08/1.93  %Foreground sorts:
% 5.08/1.93  
% 5.08/1.93  
% 5.08/1.93  %Background operators:
% 5.08/1.93  
% 5.08/1.93  
% 5.08/1.93  %Foreground operators:
% 5.08/1.93  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.08/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.08/1.93  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 5.08/1.93  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.08/1.93  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 5.08/1.93  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.08/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.08/1.93  tff('#skF_2', type, '#skF_2': $i).
% 5.08/1.93  tff('#skF_3', type, '#skF_3': $i).
% 5.08/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.08/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.08/1.93  tff('#skF_4', type, '#skF_4': $i).
% 5.08/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.08/1.93  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.08/1.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.08/1.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.08/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.08/1.93  
% 5.08/1.94  tff(f_94, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (((g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) & v1_tex_2(B, A)) => v1_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_tex_2)).
% 5.08/1.94  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 5.08/1.94  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.08/1.94  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.08/1.94  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 5.08/1.94  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 5.08/1.94  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 5.08/1.94  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.08/1.94  tff(c_28, plain, (~v1_tex_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.08/1.94  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.08/1.94  tff(c_34, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.08/1.94  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.08/1.94  tff(c_30, plain, (v1_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.08/1.94  tff(c_26, plain, (![A_16, B_22]: (m1_subset_1('#skF_1'(A_16, B_22), k1_zfmisc_1(u1_struct_0(A_16))) | v1_tex_2(B_22, A_16) | ~m1_pre_topc(B_22, A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.08/1.94  tff(c_42, plain, (![B_32, A_33]: (l1_pre_topc(B_32) | ~m1_pre_topc(B_32, A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.08/1.94  tff(c_48, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_42])).
% 5.08/1.94  tff(c_55, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_48])).
% 5.08/1.94  tff(c_16, plain, (![A_12]: (m1_pre_topc(A_12, A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.08/1.94  tff(c_91, plain, (![B_41, A_42]: (u1_struct_0(B_41)='#skF_1'(A_42, B_41) | v1_tex_2(B_41, A_42) | ~m1_pre_topc(B_41, A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.08/1.94  tff(c_94, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_91, c_28])).
% 5.08/1.94  tff(c_97, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_94])).
% 5.08/1.94  tff(c_157, plain, (![A_47, B_48]: (m1_pre_topc(A_47, g1_pre_topc(u1_struct_0(B_48), u1_pre_topc(B_48))) | ~m1_pre_topc(A_47, B_48) | ~l1_pre_topc(B_48) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.08/1.94  tff(c_169, plain, (![A_47]: (m1_pre_topc(A_47, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_47, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_47))), inference(superposition, [status(thm), theory('equality')], [c_97, c_157])).
% 5.08/1.94  tff(c_203, plain, (![A_51]: (m1_pre_topc(A_51, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_51, '#skF_4') | ~l1_pre_topc(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_169])).
% 5.08/1.94  tff(c_51, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_42])).
% 5.08/1.94  tff(c_58, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_51])).
% 5.08/1.94  tff(c_32, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.08/1.94  tff(c_74, plain, (![B_38, A_39]: (m1_pre_topc(B_38, A_39) | ~m1_pre_topc(B_38, g1_pre_topc(u1_struct_0(A_39), u1_pre_topc(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.08/1.94  tff(c_77, plain, (![B_38]: (m1_pre_topc(B_38, '#skF_3') | ~m1_pre_topc(B_38, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_74])).
% 5.08/1.94  tff(c_83, plain, (![B_38]: (m1_pre_topc(B_38, '#skF_3') | ~m1_pre_topc(B_38, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_77])).
% 5.08/1.94  tff(c_98, plain, (![B_38]: (m1_pre_topc(B_38, '#skF_3') | ~m1_pre_topc(B_38, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_83])).
% 5.08/1.94  tff(c_214, plain, (![A_51]: (m1_pre_topc(A_51, '#skF_3') | ~m1_pre_topc(A_51, '#skF_4') | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_203, c_98])).
% 5.08/1.94  tff(c_99, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_32])).
% 5.08/1.94  tff(c_166, plain, (![A_47]: (m1_pre_topc(A_47, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_47, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_47))), inference(superposition, [status(thm), theory('equality')], [c_99, c_157])).
% 5.08/1.94  tff(c_176, plain, (![A_49]: (m1_pre_topc(A_49, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_49, '#skF_3') | ~l1_pre_topc(A_49))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_166])).
% 5.08/1.94  tff(c_10, plain, (![B_8, A_6]: (m1_pre_topc(B_8, A_6) | ~m1_pre_topc(B_8, g1_pre_topc(u1_struct_0(A_6), u1_pre_topc(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.08/1.94  tff(c_103, plain, (![B_8]: (m1_pre_topc(B_8, '#skF_4') | ~m1_pre_topc(B_8, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_97, c_10])).
% 5.08/1.94  tff(c_113, plain, (![B_8]: (m1_pre_topc(B_8, '#skF_4') | ~m1_pre_topc(B_8, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_103])).
% 5.08/1.94  tff(c_189, plain, (![A_50]: (m1_pre_topc(A_50, '#skF_4') | ~m1_pre_topc(A_50, '#skF_3') | ~l1_pre_topc(A_50))), inference(resolution, [status(thm)], [c_176, c_113])).
% 5.08/1.94  tff(c_193, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_189])).
% 5.08/1.94  tff(c_196, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_193])).
% 5.08/1.94  tff(c_18, plain, (![B_15, A_13]: (r1_tarski(u1_struct_0(B_15), u1_struct_0(A_13)) | ~m1_pre_topc(B_15, A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.08/1.94  tff(c_106, plain, (![A_13]: (r1_tarski('#skF_1'('#skF_2', '#skF_4'), u1_struct_0(A_13)) | ~m1_pre_topc('#skF_4', A_13) | ~l1_pre_topc(A_13))), inference(superposition, [status(thm), theory('equality')], [c_97, c_18])).
% 5.08/1.94  tff(c_70, plain, (![B_36, A_37]: (r1_tarski(u1_struct_0(B_36), u1_struct_0(A_37)) | ~m1_pre_topc(B_36, A_37) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.08/1.94  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.08/1.94  tff(c_234, plain, (![B_56, A_57]: (u1_struct_0(B_56)=u1_struct_0(A_57) | ~r1_tarski(u1_struct_0(A_57), u1_struct_0(B_56)) | ~m1_pre_topc(B_56, A_57) | ~l1_pre_topc(A_57))), inference(resolution, [status(thm)], [c_70, c_2])).
% 5.08/1.94  tff(c_237, plain, (![B_56]: (u1_struct_0(B_56)=u1_struct_0('#skF_4') | ~r1_tarski('#skF_1'('#skF_2', '#skF_4'), u1_struct_0(B_56)) | ~m1_pre_topc(B_56, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_97, c_234])).
% 5.08/1.94  tff(c_254, plain, (![B_58]: (u1_struct_0(B_58)='#skF_1'('#skF_2', '#skF_4') | ~r1_tarski('#skF_1'('#skF_2', '#skF_4'), u1_struct_0(B_58)) | ~m1_pre_topc(B_58, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_97, c_237])).
% 5.08/1.94  tff(c_270, plain, (![A_61]: (u1_struct_0(A_61)='#skF_1'('#skF_2', '#skF_4') | ~m1_pre_topc(A_61, '#skF_4') | ~m1_pre_topc('#skF_4', A_61) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_106, c_254])).
% 5.08/1.94  tff(c_272, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_196, c_270])).
% 5.08/1.94  tff(c_278, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_272])).
% 5.08/1.94  tff(c_282, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_278])).
% 5.08/1.94  tff(c_285, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_214, c_282])).
% 5.08/1.94  tff(c_288, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_285])).
% 5.08/1.94  tff(c_292, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_288])).
% 5.08/1.94  tff(c_296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_292])).
% 5.08/1.94  tff(c_297, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_278])).
% 5.08/1.94  tff(c_392, plain, (![B_64, A_65]: (v1_subset_1(u1_struct_0(B_64), u1_struct_0(A_65)) | ~m1_subset_1(u1_struct_0(B_64), k1_zfmisc_1(u1_struct_0(A_65))) | ~v1_tex_2(B_64, A_65) | ~m1_pre_topc(B_64, A_65) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.08/1.94  tff(c_395, plain, (![A_65]: (v1_subset_1(u1_struct_0('#skF_3'), u1_struct_0(A_65)) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_65))) | ~v1_tex_2('#skF_3', A_65) | ~m1_pre_topc('#skF_3', A_65) | ~l1_pre_topc(A_65))), inference(superposition, [status(thm), theory('equality')], [c_297, c_392])).
% 5.08/1.94  tff(c_2349, plain, (![A_138]: (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), u1_struct_0(A_138)) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_138))) | ~v1_tex_2('#skF_3', A_138) | ~m1_pre_topc('#skF_3', A_138) | ~l1_pre_topc(A_138))), inference(demodulation, [status(thm), theory('equality')], [c_297, c_395])).
% 5.08/1.94  tff(c_2356, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | v1_tex_2('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_2349])).
% 5.08/1.94  tff(c_2364, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | v1_tex_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_36, c_30, c_2356])).
% 5.08/1.94  tff(c_2365, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_28, c_2364])).
% 5.08/1.94  tff(c_22, plain, (![A_16, B_22]: (~v1_subset_1('#skF_1'(A_16, B_22), u1_struct_0(A_16)) | v1_tex_2(B_22, A_16) | ~m1_pre_topc(B_22, A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.08/1.94  tff(c_2370, plain, (v1_tex_2('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2365, c_22])).
% 5.08/1.94  tff(c_2373, plain, (v1_tex_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_2370])).
% 5.08/1.94  tff(c_2375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_2373])).
% 5.08/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.08/1.94  
% 5.08/1.94  Inference rules
% 5.08/1.94  ----------------------
% 5.08/1.94  #Ref     : 0
% 5.08/1.94  #Sup     : 451
% 5.08/1.94  #Fact    : 0
% 5.08/1.94  #Define  : 0
% 5.08/1.94  #Split   : 9
% 5.08/1.94  #Chain   : 0
% 5.08/1.94  #Close   : 0
% 5.08/1.94  
% 5.08/1.94  Ordering : KBO
% 5.08/1.94  
% 5.08/1.94  Simplification rules
% 5.08/1.94  ----------------------
% 5.08/1.94  #Subsume      : 215
% 5.08/1.94  #Demod        : 1514
% 5.08/1.94  #Tautology    : 139
% 5.08/1.94  #SimpNegUnit  : 33
% 5.08/1.94  #BackRed      : 51
% 5.08/1.94  
% 5.08/1.94  #Partial instantiations: 0
% 5.08/1.94  #Strategies tried      : 1
% 5.08/1.94  
% 5.08/1.94  Timing (in seconds)
% 5.08/1.94  ----------------------
% 5.08/1.95  Preprocessing        : 0.32
% 5.08/1.95  Parsing              : 0.16
% 5.08/1.95  CNF conversion       : 0.02
% 5.08/1.95  Main loop            : 0.85
% 5.08/1.95  Inferencing          : 0.24
% 5.08/1.95  Reduction            : 0.37
% 5.08/1.95  Demodulation         : 0.28
% 5.08/1.95  BG Simplification    : 0.03
% 5.08/1.95  Subsumption          : 0.17
% 5.08/1.95  Abstraction          : 0.04
% 5.08/1.95  MUC search           : 0.00
% 5.08/1.95  Cooper               : 0.00
% 5.08/1.95  Total                : 1.21
% 5.08/1.95  Index Insertion      : 0.00
% 5.08/1.95  Index Deletion       : 0.00
% 5.08/1.95  Index Matching       : 0.00
% 5.08/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
