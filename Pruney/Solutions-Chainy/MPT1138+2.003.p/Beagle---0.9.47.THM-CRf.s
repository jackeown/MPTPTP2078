%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:20 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 280 expanded)
%              Number of leaves         :   32 ( 116 expanded)
%              Depth                    :   19
%              Number of atoms          :  222 (1023 expanded)
%              Number of equality atoms :    3 (  25 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r8_relat_2 > r2_hidden > m1_subset_1 > v4_orders_2 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(r8_relat_2,type,(
    r8_relat_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( v4_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r1_orders_2(A,B,C)
                        & r1_orders_2(A,C,D) )
                     => r1_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ~ ( r2_hidden(A,D)
          & ! [E,F] :
              ~ ( A = k4_tarski(E,F)
                & r2_hidden(E,B)
                & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v4_orders_2(A)
      <=> r8_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_orders_2)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r8_relat_2(A,B)
        <=> ! [C,D,E] :
              ( ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & r2_hidden(E,B)
                & r2_hidden(k4_tarski(C,D),A)
                & r2_hidden(k4_tarski(D,E),A) )
             => r2_hidden(k4_tarski(C,E),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_2)).

tff(c_40,plain,(
    ~ r1_orders_2('#skF_6','#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44,plain,(
    r1_orders_2('#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_52,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_48,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_36,plain,(
    ! [B_43,C_45,A_39] :
      ( r2_hidden(k4_tarski(B_43,C_45),u1_orders_2(A_39))
      | ~ r1_orders_2(A_39,B_43,C_45)
      | ~ m1_subset_1(C_45,u1_struct_0(A_39))
      | ~ m1_subset_1(B_43,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_38,plain,(
    ! [A_46] :
      ( m1_subset_1(u1_orders_2(A_46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_46),u1_struct_0(A_46))))
      | ~ l1_orders_2(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_114,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( r2_hidden('#skF_1'(A_93,B_94,C_95,D_96),B_94)
      | ~ r2_hidden(A_93,D_96)
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(B_94,C_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_117,plain,(
    ! [A_93,A_46] :
      ( r2_hidden('#skF_1'(A_93,u1_struct_0(A_46),u1_struct_0(A_46),u1_orders_2(A_46)),u1_struct_0(A_46))
      | ~ r2_hidden(A_93,u1_orders_2(A_46))
      | ~ l1_orders_2(A_46) ) ),
    inference(resolution,[status(thm)],[c_38,c_114])).

tff(c_110,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( r2_hidden('#skF_2'(A_89,B_90,C_91,D_92),C_91)
      | ~ r2_hidden(A_89,D_92)
      | ~ m1_subset_1(D_92,k1_zfmisc_1(k2_zfmisc_1(B_90,C_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_113,plain,(
    ! [A_89,A_46] :
      ( r2_hidden('#skF_2'(A_89,u1_struct_0(A_46),u1_struct_0(A_46),u1_orders_2(A_46)),u1_struct_0(A_46))
      | ~ r2_hidden(A_89,u1_orders_2(A_46))
      | ~ l1_orders_2(A_46) ) ),
    inference(resolution,[status(thm)],[c_38,c_110])).

tff(c_145,plain,(
    ! [A_119,B_120,C_121,D_122] :
      ( k4_tarski('#skF_1'(A_119,B_120,C_121,D_122),'#skF_2'(A_119,B_120,C_121,D_122)) = A_119
      | ~ r2_hidden(A_119,D_122)
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k2_zfmisc_1(B_120,C_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_181,plain,(
    ! [A_137,A_138] :
      ( k4_tarski('#skF_1'(A_137,u1_struct_0(A_138),u1_struct_0(A_138),u1_orders_2(A_138)),'#skF_2'(A_137,u1_struct_0(A_138),u1_struct_0(A_138),u1_orders_2(A_138))) = A_137
      | ~ r2_hidden(A_137,u1_orders_2(A_138))
      | ~ l1_orders_2(A_138) ) ),
    inference(resolution,[status(thm)],[c_38,c_145])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4))
      | ~ r2_hidden(B_2,D_4)
      | ~ r2_hidden(A_1,C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_311,plain,(
    ! [A_157,C_158,D_159,A_160] :
      ( r2_hidden(A_157,k2_zfmisc_1(C_158,D_159))
      | ~ r2_hidden('#skF_2'(A_157,u1_struct_0(A_160),u1_struct_0(A_160),u1_orders_2(A_160)),D_159)
      | ~ r2_hidden('#skF_1'(A_157,u1_struct_0(A_160),u1_struct_0(A_160),u1_orders_2(A_160)),C_158)
      | ~ r2_hidden(A_157,u1_orders_2(A_160))
      | ~ l1_orders_2(A_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_2])).

tff(c_316,plain,(
    ! [A_163,C_164,A_165] :
      ( r2_hidden(A_163,k2_zfmisc_1(C_164,u1_struct_0(A_165)))
      | ~ r2_hidden('#skF_1'(A_163,u1_struct_0(A_165),u1_struct_0(A_165),u1_orders_2(A_165)),C_164)
      | ~ r2_hidden(A_163,u1_orders_2(A_165))
      | ~ l1_orders_2(A_165) ) ),
    inference(resolution,[status(thm)],[c_113,c_311])).

tff(c_321,plain,(
    ! [A_166,A_167] :
      ( r2_hidden(A_166,k2_zfmisc_1(u1_struct_0(A_167),u1_struct_0(A_167)))
      | ~ r2_hidden(A_166,u1_orders_2(A_167))
      | ~ l1_orders_2(A_167) ) ),
    inference(resolution,[status(thm)],[c_117,c_316])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_380,plain,(
    ! [A_171,A_172,B_173] :
      ( r2_hidden(A_171,u1_struct_0(A_172))
      | ~ r2_hidden(k4_tarski(A_171,B_173),u1_orders_2(A_172))
      | ~ l1_orders_2(A_172) ) ),
    inference(resolution,[status(thm)],[c_321,c_6])).

tff(c_419,plain,(
    ! [B_180,A_181,C_182] :
      ( r2_hidden(B_180,u1_struct_0(A_181))
      | ~ r1_orders_2(A_181,B_180,C_182)
      | ~ m1_subset_1(C_182,u1_struct_0(A_181))
      | ~ m1_subset_1(B_180,u1_struct_0(A_181))
      | ~ l1_orders_2(A_181) ) ),
    inference(resolution,[status(thm)],[c_36,c_380])).

tff(c_423,plain,
    ( r2_hidden('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_419])).

tff(c_429,plain,(
    r2_hidden('#skF_7',u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_423])).

tff(c_46,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_67,plain,(
    ! [A_77] :
      ( m1_subset_1(u1_orders_2(A_77),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_77),u1_struct_0(A_77))))
      | ~ l1_orders_2(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    ! [A_77] :
      ( v1_relat_1(u1_orders_2(A_77))
      | ~ l1_orders_2(A_77) ) ),
    inference(resolution,[status(thm)],[c_67,c_8])).

tff(c_54,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_42,plain,(
    r1_orders_2('#skF_6','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_32,plain,(
    ! [A_38] :
      ( r8_relat_2(u1_orders_2(A_38),u1_struct_0(A_38))
      | ~ v4_orders_2(A_38)
      | ~ l1_orders_2(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_425,plain,
    ( r2_hidden('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_419])).

tff(c_432,plain,(
    r2_hidden('#skF_8',u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_46,c_425])).

tff(c_4,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_362,plain,(
    ! [B_168,A_169,A_170] :
      ( r2_hidden(B_168,u1_struct_0(A_169))
      | ~ r2_hidden(k4_tarski(A_170,B_168),u1_orders_2(A_169))
      | ~ l1_orders_2(A_169) ) ),
    inference(resolution,[status(thm)],[c_321,c_4])).

tff(c_449,plain,(
    ! [C_185,A_186,B_187] :
      ( r2_hidden(C_185,u1_struct_0(A_186))
      | ~ r1_orders_2(A_186,B_187,C_185)
      | ~ m1_subset_1(C_185,u1_struct_0(A_186))
      | ~ m1_subset_1(B_187,u1_struct_0(A_186))
      | ~ l1_orders_2(A_186) ) ),
    inference(resolution,[status(thm)],[c_36,c_362])).

tff(c_457,plain,
    ( r2_hidden('#skF_9',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_449])).

tff(c_465,plain,(
    r2_hidden('#skF_9',u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_46,c_457])).

tff(c_167,plain,(
    ! [B_133,A_132,D_131,C_130,E_129] :
      ( r2_hidden(k4_tarski(C_130,E_129),A_132)
      | ~ r2_hidden(k4_tarski(D_131,E_129),A_132)
      | ~ r2_hidden(k4_tarski(C_130,D_131),A_132)
      | ~ r2_hidden(E_129,B_133)
      | ~ r2_hidden(D_131,B_133)
      | ~ r2_hidden(C_130,B_133)
      | ~ r8_relat_2(A_132,B_133)
      | ~ v1_relat_1(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1564,plain,(
    ! [B_334,A_333,C_335,B_337,C_336] :
      ( r2_hidden(k4_tarski(C_336,C_335),u1_orders_2(A_333))
      | ~ r2_hidden(k4_tarski(C_336,B_334),u1_orders_2(A_333))
      | ~ r2_hidden(C_335,B_337)
      | ~ r2_hidden(B_334,B_337)
      | ~ r2_hidden(C_336,B_337)
      | ~ r8_relat_2(u1_orders_2(A_333),B_337)
      | ~ v1_relat_1(u1_orders_2(A_333))
      | ~ r1_orders_2(A_333,B_334,C_335)
      | ~ m1_subset_1(C_335,u1_struct_0(A_333))
      | ~ m1_subset_1(B_334,u1_struct_0(A_333))
      | ~ l1_orders_2(A_333) ) ),
    inference(resolution,[status(thm)],[c_36,c_167])).

tff(c_2123,plain,(
    ! [B_386,A_385,C_387,B_389,C_388] :
      ( r2_hidden(k4_tarski(B_386,C_387),u1_orders_2(A_385))
      | ~ r2_hidden(C_387,B_389)
      | ~ r2_hidden(C_388,B_389)
      | ~ r2_hidden(B_386,B_389)
      | ~ r8_relat_2(u1_orders_2(A_385),B_389)
      | ~ v1_relat_1(u1_orders_2(A_385))
      | ~ r1_orders_2(A_385,C_388,C_387)
      | ~ m1_subset_1(C_387,u1_struct_0(A_385))
      | ~ r1_orders_2(A_385,B_386,C_388)
      | ~ m1_subset_1(C_388,u1_struct_0(A_385))
      | ~ m1_subset_1(B_386,u1_struct_0(A_385))
      | ~ l1_orders_2(A_385) ) ),
    inference(resolution,[status(thm)],[c_36,c_1564])).

tff(c_6582,plain,(
    ! [B_565,A_566,C_567] :
      ( r2_hidden(k4_tarski(B_565,'#skF_9'),u1_orders_2(A_566))
      | ~ r2_hidden(C_567,u1_struct_0('#skF_6'))
      | ~ r2_hidden(B_565,u1_struct_0('#skF_6'))
      | ~ r8_relat_2(u1_orders_2(A_566),u1_struct_0('#skF_6'))
      | ~ v1_relat_1(u1_orders_2(A_566))
      | ~ r1_orders_2(A_566,C_567,'#skF_9')
      | ~ m1_subset_1('#skF_9',u1_struct_0(A_566))
      | ~ r1_orders_2(A_566,B_565,C_567)
      | ~ m1_subset_1(C_567,u1_struct_0(A_566))
      | ~ m1_subset_1(B_565,u1_struct_0(A_566))
      | ~ l1_orders_2(A_566) ) ),
    inference(resolution,[status(thm)],[c_465,c_2123])).

tff(c_7480,plain,(
    ! [B_601,A_602] :
      ( r2_hidden(k4_tarski(B_601,'#skF_9'),u1_orders_2(A_602))
      | ~ r2_hidden(B_601,u1_struct_0('#skF_6'))
      | ~ r8_relat_2(u1_orders_2(A_602),u1_struct_0('#skF_6'))
      | ~ v1_relat_1(u1_orders_2(A_602))
      | ~ r1_orders_2(A_602,'#skF_8','#skF_9')
      | ~ m1_subset_1('#skF_9',u1_struct_0(A_602))
      | ~ r1_orders_2(A_602,B_601,'#skF_8')
      | ~ m1_subset_1('#skF_8',u1_struct_0(A_602))
      | ~ m1_subset_1(B_601,u1_struct_0(A_602))
      | ~ l1_orders_2(A_602) ) ),
    inference(resolution,[status(thm)],[c_432,c_6582])).

tff(c_7483,plain,(
    ! [B_601] :
      ( r2_hidden(k4_tarski(B_601,'#skF_9'),u1_orders_2('#skF_6'))
      | ~ r2_hidden(B_601,u1_struct_0('#skF_6'))
      | ~ v1_relat_1(u1_orders_2('#skF_6'))
      | ~ r1_orders_2('#skF_6','#skF_8','#skF_9')
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
      | ~ r1_orders_2('#skF_6',B_601,'#skF_8')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_601,u1_struct_0('#skF_6'))
      | ~ v4_orders_2('#skF_6')
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_7480])).

tff(c_7486,plain,(
    ! [B_601] :
      ( r2_hidden(k4_tarski(B_601,'#skF_9'),u1_orders_2('#skF_6'))
      | ~ r2_hidden(B_601,u1_struct_0('#skF_6'))
      | ~ v1_relat_1(u1_orders_2('#skF_6'))
      | ~ r1_orders_2('#skF_6',B_601,'#skF_8')
      | ~ m1_subset_1(B_601,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_48,c_46,c_42,c_7483])).

tff(c_7487,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_7486])).

tff(c_7490,plain,(
    ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_71,c_7487])).

tff(c_7494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_7490])).

tff(c_7497,plain,(
    ! [B_603] :
      ( r2_hidden(k4_tarski(B_603,'#skF_9'),u1_orders_2('#skF_6'))
      | ~ r2_hidden(B_603,u1_struct_0('#skF_6'))
      | ~ r1_orders_2('#skF_6',B_603,'#skF_8')
      | ~ m1_subset_1(B_603,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_7486])).

tff(c_34,plain,(
    ! [A_39,B_43,C_45] :
      ( r1_orders_2(A_39,B_43,C_45)
      | ~ r2_hidden(k4_tarski(B_43,C_45),u1_orders_2(A_39))
      | ~ m1_subset_1(C_45,u1_struct_0(A_39))
      | ~ m1_subset_1(B_43,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_7538,plain,(
    ! [B_603] :
      ( r1_orders_2('#skF_6',B_603,'#skF_9')
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ r2_hidden(B_603,u1_struct_0('#skF_6'))
      | ~ r1_orders_2('#skF_6',B_603,'#skF_8')
      | ~ m1_subset_1(B_603,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_7497,c_34])).

tff(c_7568,plain,(
    ! [B_604] :
      ( r1_orders_2('#skF_6',B_604,'#skF_9')
      | ~ r2_hidden(B_604,u1_struct_0('#skF_6'))
      | ~ r1_orders_2('#skF_6',B_604,'#skF_8')
      | ~ m1_subset_1(B_604,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_7538])).

tff(c_7729,plain,
    ( r1_orders_2('#skF_6','#skF_7','#skF_9')
    | ~ r1_orders_2('#skF_6','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_429,c_7568])).

tff(c_7820,plain,(
    r1_orders_2('#skF_6','#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_7729])).

tff(c_7822,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_7820])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:25:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.81/2.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.81/3.00  
% 7.81/3.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.81/3.00  %$ r1_orders_2 > r8_relat_2 > r2_hidden > m1_subset_1 > v4_orders_2 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 7.81/3.00  
% 7.81/3.00  %Foreground sorts:
% 7.81/3.00  
% 7.81/3.00  
% 7.81/3.00  %Background operators:
% 7.81/3.00  
% 7.81/3.00  
% 7.81/3.00  %Foreground operators:
% 7.81/3.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.81/3.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.81/3.00  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.81/3.00  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 7.81/3.00  tff('#skF_7', type, '#skF_7': $i).
% 7.81/3.00  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.81/3.00  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 7.81/3.00  tff('#skF_6', type, '#skF_6': $i).
% 7.81/3.00  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.81/3.00  tff('#skF_9', type, '#skF_9': $i).
% 7.81/3.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.81/3.00  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.81/3.00  tff('#skF_8', type, '#skF_8': $i).
% 7.81/3.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.81/3.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.81/3.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.81/3.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.81/3.00  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 7.81/3.00  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 7.81/3.00  tff(r8_relat_2, type, r8_relat_2: ($i * $i) > $o).
% 7.81/3.00  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.81/3.00  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.81/3.00  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.81/3.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.81/3.00  
% 7.81/3.02  tff(f_108, negated_conjecture, ~(![A]: ((v4_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, D)) => r1_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_orders_2)).
% 7.81/3.02  tff(f_84, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 7.81/3.02  tff(f_88, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 7.81/3.02  tff(f_48, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_relset_1)).
% 7.81/3.02  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 7.81/3.02  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.81/3.02  tff(f_72, axiom, (![A]: (l1_orders_2(A) => (v4_orders_2(A) <=> r8_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_orders_2)).
% 7.81/3.02  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (r8_relat_2(A, B) <=> (![C, D, E]: (((((r2_hidden(C, B) & r2_hidden(D, B)) & r2_hidden(E, B)) & r2_hidden(k4_tarski(C, D), A)) & r2_hidden(k4_tarski(D, E), A)) => r2_hidden(k4_tarski(C, E), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_2)).
% 7.81/3.02  tff(c_40, plain, (~r1_orders_2('#skF_6', '#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.81/3.02  tff(c_50, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.81/3.02  tff(c_44, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.81/3.02  tff(c_52, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.81/3.02  tff(c_48, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.81/3.02  tff(c_36, plain, (![B_43, C_45, A_39]: (r2_hidden(k4_tarski(B_43, C_45), u1_orders_2(A_39)) | ~r1_orders_2(A_39, B_43, C_45) | ~m1_subset_1(C_45, u1_struct_0(A_39)) | ~m1_subset_1(B_43, u1_struct_0(A_39)) | ~l1_orders_2(A_39))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.81/3.02  tff(c_38, plain, (![A_46]: (m1_subset_1(u1_orders_2(A_46), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_46), u1_struct_0(A_46)))) | ~l1_orders_2(A_46))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.81/3.02  tff(c_114, plain, (![A_93, B_94, C_95, D_96]: (r2_hidden('#skF_1'(A_93, B_94, C_95, D_96), B_94) | ~r2_hidden(A_93, D_96) | ~m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(B_94, C_95))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.81/3.02  tff(c_117, plain, (![A_93, A_46]: (r2_hidden('#skF_1'(A_93, u1_struct_0(A_46), u1_struct_0(A_46), u1_orders_2(A_46)), u1_struct_0(A_46)) | ~r2_hidden(A_93, u1_orders_2(A_46)) | ~l1_orders_2(A_46))), inference(resolution, [status(thm)], [c_38, c_114])).
% 7.81/3.02  tff(c_110, plain, (![A_89, B_90, C_91, D_92]: (r2_hidden('#skF_2'(A_89, B_90, C_91, D_92), C_91) | ~r2_hidden(A_89, D_92) | ~m1_subset_1(D_92, k1_zfmisc_1(k2_zfmisc_1(B_90, C_91))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.81/3.02  tff(c_113, plain, (![A_89, A_46]: (r2_hidden('#skF_2'(A_89, u1_struct_0(A_46), u1_struct_0(A_46), u1_orders_2(A_46)), u1_struct_0(A_46)) | ~r2_hidden(A_89, u1_orders_2(A_46)) | ~l1_orders_2(A_46))), inference(resolution, [status(thm)], [c_38, c_110])).
% 7.81/3.02  tff(c_145, plain, (![A_119, B_120, C_121, D_122]: (k4_tarski('#skF_1'(A_119, B_120, C_121, D_122), '#skF_2'(A_119, B_120, C_121, D_122))=A_119 | ~r2_hidden(A_119, D_122) | ~m1_subset_1(D_122, k1_zfmisc_1(k2_zfmisc_1(B_120, C_121))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.81/3.02  tff(c_181, plain, (![A_137, A_138]: (k4_tarski('#skF_1'(A_137, u1_struct_0(A_138), u1_struct_0(A_138), u1_orders_2(A_138)), '#skF_2'(A_137, u1_struct_0(A_138), u1_struct_0(A_138), u1_orders_2(A_138)))=A_137 | ~r2_hidden(A_137, u1_orders_2(A_138)) | ~l1_orders_2(A_138))), inference(resolution, [status(thm)], [c_38, c_145])).
% 7.81/3.02  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)) | ~r2_hidden(B_2, D_4) | ~r2_hidden(A_1, C_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.81/3.02  tff(c_311, plain, (![A_157, C_158, D_159, A_160]: (r2_hidden(A_157, k2_zfmisc_1(C_158, D_159)) | ~r2_hidden('#skF_2'(A_157, u1_struct_0(A_160), u1_struct_0(A_160), u1_orders_2(A_160)), D_159) | ~r2_hidden('#skF_1'(A_157, u1_struct_0(A_160), u1_struct_0(A_160), u1_orders_2(A_160)), C_158) | ~r2_hidden(A_157, u1_orders_2(A_160)) | ~l1_orders_2(A_160))), inference(superposition, [status(thm), theory('equality')], [c_181, c_2])).
% 7.81/3.02  tff(c_316, plain, (![A_163, C_164, A_165]: (r2_hidden(A_163, k2_zfmisc_1(C_164, u1_struct_0(A_165))) | ~r2_hidden('#skF_1'(A_163, u1_struct_0(A_165), u1_struct_0(A_165), u1_orders_2(A_165)), C_164) | ~r2_hidden(A_163, u1_orders_2(A_165)) | ~l1_orders_2(A_165))), inference(resolution, [status(thm)], [c_113, c_311])).
% 7.81/3.02  tff(c_321, plain, (![A_166, A_167]: (r2_hidden(A_166, k2_zfmisc_1(u1_struct_0(A_167), u1_struct_0(A_167))) | ~r2_hidden(A_166, u1_orders_2(A_167)) | ~l1_orders_2(A_167))), inference(resolution, [status(thm)], [c_117, c_316])).
% 7.81/3.02  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.81/3.02  tff(c_380, plain, (![A_171, A_172, B_173]: (r2_hidden(A_171, u1_struct_0(A_172)) | ~r2_hidden(k4_tarski(A_171, B_173), u1_orders_2(A_172)) | ~l1_orders_2(A_172))), inference(resolution, [status(thm)], [c_321, c_6])).
% 7.81/3.02  tff(c_419, plain, (![B_180, A_181, C_182]: (r2_hidden(B_180, u1_struct_0(A_181)) | ~r1_orders_2(A_181, B_180, C_182) | ~m1_subset_1(C_182, u1_struct_0(A_181)) | ~m1_subset_1(B_180, u1_struct_0(A_181)) | ~l1_orders_2(A_181))), inference(resolution, [status(thm)], [c_36, c_380])).
% 7.81/3.02  tff(c_423, plain, (r2_hidden('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_44, c_419])).
% 7.81/3.02  tff(c_429, plain, (r2_hidden('#skF_7', u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_423])).
% 7.81/3.02  tff(c_46, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.81/3.02  tff(c_67, plain, (![A_77]: (m1_subset_1(u1_orders_2(A_77), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_77), u1_struct_0(A_77)))) | ~l1_orders_2(A_77))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.81/3.02  tff(c_8, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.81/3.02  tff(c_71, plain, (![A_77]: (v1_relat_1(u1_orders_2(A_77)) | ~l1_orders_2(A_77))), inference(resolution, [status(thm)], [c_67, c_8])).
% 7.81/3.02  tff(c_54, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.81/3.02  tff(c_42, plain, (r1_orders_2('#skF_6', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.81/3.02  tff(c_32, plain, (![A_38]: (r8_relat_2(u1_orders_2(A_38), u1_struct_0(A_38)) | ~v4_orders_2(A_38) | ~l1_orders_2(A_38))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.81/3.02  tff(c_425, plain, (r2_hidden('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_42, c_419])).
% 7.81/3.02  tff(c_432, plain, (r2_hidden('#skF_8', u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_46, c_425])).
% 7.81/3.02  tff(c_4, plain, (![B_2, D_4, A_1, C_3]: (r2_hidden(B_2, D_4) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.81/3.02  tff(c_362, plain, (![B_168, A_169, A_170]: (r2_hidden(B_168, u1_struct_0(A_169)) | ~r2_hidden(k4_tarski(A_170, B_168), u1_orders_2(A_169)) | ~l1_orders_2(A_169))), inference(resolution, [status(thm)], [c_321, c_4])).
% 7.81/3.02  tff(c_449, plain, (![C_185, A_186, B_187]: (r2_hidden(C_185, u1_struct_0(A_186)) | ~r1_orders_2(A_186, B_187, C_185) | ~m1_subset_1(C_185, u1_struct_0(A_186)) | ~m1_subset_1(B_187, u1_struct_0(A_186)) | ~l1_orders_2(A_186))), inference(resolution, [status(thm)], [c_36, c_362])).
% 7.81/3.02  tff(c_457, plain, (r2_hidden('#skF_9', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_42, c_449])).
% 7.81/3.02  tff(c_465, plain, (r2_hidden('#skF_9', u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_46, c_457])).
% 7.81/3.02  tff(c_167, plain, (![B_133, A_132, D_131, C_130, E_129]: (r2_hidden(k4_tarski(C_130, E_129), A_132) | ~r2_hidden(k4_tarski(D_131, E_129), A_132) | ~r2_hidden(k4_tarski(C_130, D_131), A_132) | ~r2_hidden(E_129, B_133) | ~r2_hidden(D_131, B_133) | ~r2_hidden(C_130, B_133) | ~r8_relat_2(A_132, B_133) | ~v1_relat_1(A_132))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.81/3.02  tff(c_1564, plain, (![B_334, A_333, C_335, B_337, C_336]: (r2_hidden(k4_tarski(C_336, C_335), u1_orders_2(A_333)) | ~r2_hidden(k4_tarski(C_336, B_334), u1_orders_2(A_333)) | ~r2_hidden(C_335, B_337) | ~r2_hidden(B_334, B_337) | ~r2_hidden(C_336, B_337) | ~r8_relat_2(u1_orders_2(A_333), B_337) | ~v1_relat_1(u1_orders_2(A_333)) | ~r1_orders_2(A_333, B_334, C_335) | ~m1_subset_1(C_335, u1_struct_0(A_333)) | ~m1_subset_1(B_334, u1_struct_0(A_333)) | ~l1_orders_2(A_333))), inference(resolution, [status(thm)], [c_36, c_167])).
% 7.81/3.02  tff(c_2123, plain, (![B_386, A_385, C_387, B_389, C_388]: (r2_hidden(k4_tarski(B_386, C_387), u1_orders_2(A_385)) | ~r2_hidden(C_387, B_389) | ~r2_hidden(C_388, B_389) | ~r2_hidden(B_386, B_389) | ~r8_relat_2(u1_orders_2(A_385), B_389) | ~v1_relat_1(u1_orders_2(A_385)) | ~r1_orders_2(A_385, C_388, C_387) | ~m1_subset_1(C_387, u1_struct_0(A_385)) | ~r1_orders_2(A_385, B_386, C_388) | ~m1_subset_1(C_388, u1_struct_0(A_385)) | ~m1_subset_1(B_386, u1_struct_0(A_385)) | ~l1_orders_2(A_385))), inference(resolution, [status(thm)], [c_36, c_1564])).
% 7.81/3.02  tff(c_6582, plain, (![B_565, A_566, C_567]: (r2_hidden(k4_tarski(B_565, '#skF_9'), u1_orders_2(A_566)) | ~r2_hidden(C_567, u1_struct_0('#skF_6')) | ~r2_hidden(B_565, u1_struct_0('#skF_6')) | ~r8_relat_2(u1_orders_2(A_566), u1_struct_0('#skF_6')) | ~v1_relat_1(u1_orders_2(A_566)) | ~r1_orders_2(A_566, C_567, '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0(A_566)) | ~r1_orders_2(A_566, B_565, C_567) | ~m1_subset_1(C_567, u1_struct_0(A_566)) | ~m1_subset_1(B_565, u1_struct_0(A_566)) | ~l1_orders_2(A_566))), inference(resolution, [status(thm)], [c_465, c_2123])).
% 7.81/3.02  tff(c_7480, plain, (![B_601, A_602]: (r2_hidden(k4_tarski(B_601, '#skF_9'), u1_orders_2(A_602)) | ~r2_hidden(B_601, u1_struct_0('#skF_6')) | ~r8_relat_2(u1_orders_2(A_602), u1_struct_0('#skF_6')) | ~v1_relat_1(u1_orders_2(A_602)) | ~r1_orders_2(A_602, '#skF_8', '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0(A_602)) | ~r1_orders_2(A_602, B_601, '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0(A_602)) | ~m1_subset_1(B_601, u1_struct_0(A_602)) | ~l1_orders_2(A_602))), inference(resolution, [status(thm)], [c_432, c_6582])).
% 7.81/3.02  tff(c_7483, plain, (![B_601]: (r2_hidden(k4_tarski(B_601, '#skF_9'), u1_orders_2('#skF_6')) | ~r2_hidden(B_601, u1_struct_0('#skF_6')) | ~v1_relat_1(u1_orders_2('#skF_6')) | ~r1_orders_2('#skF_6', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~r1_orders_2('#skF_6', B_601, '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1(B_601, u1_struct_0('#skF_6')) | ~v4_orders_2('#skF_6') | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_32, c_7480])).
% 7.81/3.02  tff(c_7486, plain, (![B_601]: (r2_hidden(k4_tarski(B_601, '#skF_9'), u1_orders_2('#skF_6')) | ~r2_hidden(B_601, u1_struct_0('#skF_6')) | ~v1_relat_1(u1_orders_2('#skF_6')) | ~r1_orders_2('#skF_6', B_601, '#skF_8') | ~m1_subset_1(B_601, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_48, c_46, c_42, c_7483])).
% 7.81/3.02  tff(c_7487, plain, (~v1_relat_1(u1_orders_2('#skF_6'))), inference(splitLeft, [status(thm)], [c_7486])).
% 7.81/3.02  tff(c_7490, plain, (~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_71, c_7487])).
% 7.81/3.02  tff(c_7494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_7490])).
% 7.81/3.02  tff(c_7497, plain, (![B_603]: (r2_hidden(k4_tarski(B_603, '#skF_9'), u1_orders_2('#skF_6')) | ~r2_hidden(B_603, u1_struct_0('#skF_6')) | ~r1_orders_2('#skF_6', B_603, '#skF_8') | ~m1_subset_1(B_603, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_7486])).
% 7.81/3.02  tff(c_34, plain, (![A_39, B_43, C_45]: (r1_orders_2(A_39, B_43, C_45) | ~r2_hidden(k4_tarski(B_43, C_45), u1_orders_2(A_39)) | ~m1_subset_1(C_45, u1_struct_0(A_39)) | ~m1_subset_1(B_43, u1_struct_0(A_39)) | ~l1_orders_2(A_39))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.81/3.02  tff(c_7538, plain, (![B_603]: (r1_orders_2('#skF_6', B_603, '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~r2_hidden(B_603, u1_struct_0('#skF_6')) | ~r1_orders_2('#skF_6', B_603, '#skF_8') | ~m1_subset_1(B_603, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_7497, c_34])).
% 7.81/3.02  tff(c_7568, plain, (![B_604]: (r1_orders_2('#skF_6', B_604, '#skF_9') | ~r2_hidden(B_604, u1_struct_0('#skF_6')) | ~r1_orders_2('#skF_6', B_604, '#skF_8') | ~m1_subset_1(B_604, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_7538])).
% 7.81/3.02  tff(c_7729, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_9') | ~r1_orders_2('#skF_6', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_429, c_7568])).
% 7.81/3.02  tff(c_7820, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_7729])).
% 7.81/3.02  tff(c_7822, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_7820])).
% 7.81/3.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.81/3.02  
% 7.81/3.02  Inference rules
% 7.81/3.02  ----------------------
% 7.81/3.02  #Ref     : 0
% 7.81/3.02  #Sup     : 2292
% 7.81/3.02  #Fact    : 0
% 7.81/3.02  #Define  : 0
% 7.81/3.02  #Split   : 3
% 7.81/3.02  #Chain   : 0
% 7.81/3.02  #Close   : 0
% 7.81/3.02  
% 7.81/3.02  Ordering : KBO
% 7.81/3.02  
% 7.81/3.02  Simplification rules
% 7.81/3.02  ----------------------
% 7.81/3.02  #Subsume      : 649
% 7.81/3.02  #Demod        : 57
% 7.81/3.02  #Tautology    : 31
% 7.81/3.02  #SimpNegUnit  : 1
% 7.81/3.02  #BackRed      : 0
% 7.81/3.02  
% 7.81/3.02  #Partial instantiations: 0
% 7.81/3.02  #Strategies tried      : 1
% 7.81/3.02  
% 7.81/3.02  Timing (in seconds)
% 7.81/3.02  ----------------------
% 7.81/3.03  Preprocessing        : 0.28
% 7.81/3.03  Parsing              : 0.15
% 7.81/3.03  CNF conversion       : 0.02
% 7.81/3.03  Main loop            : 1.91
% 7.81/3.03  Inferencing          : 0.48
% 7.81/3.03  Reduction            : 0.52
% 7.81/3.03  Demodulation         : 0.36
% 7.81/3.03  BG Simplification    : 0.07
% 7.81/3.03  Subsumption          : 0.70
% 7.81/3.03  Abstraction          : 0.10
% 7.81/3.03  MUC search           : 0.00
% 7.81/3.03  Cooper               : 0.00
% 7.81/3.03  Total                : 2.23
% 7.81/3.03  Index Insertion      : 0.00
% 7.81/3.03  Index Deletion       : 0.00
% 7.81/3.03  Index Matching       : 0.00
% 7.81/3.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
