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
% DateTime   : Thu Dec  3 10:20:11 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 233 expanded)
%              Number of leaves         :   39 (  98 expanded)
%              Depth                    :   12
%              Number of atoms          :  147 ( 663 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r8_relat_2 > r7_relat_2 > r6_relat_2 > r4_relat_2 > r3_orders_1 > r2_hidden > r1_tarski > r1_relat_2 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_relat_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r3_orders_1,type,(
    r3_orders_1: ( $i * $i ) > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r4_relat_2,type,(
    r4_relat_2: ( $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r6_relat_2,type,(
    r6_relat_2: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_relat_2,type,(
    r1_relat_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(r7_relat_2,type,(
    r7_relat_2: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(r8_relat_2,type,(
    r8_relat_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( v6_orders_2(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => r3_orders_1(u1_orders_2(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_orders_2)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v5_orders_2(A)
      <=> r4_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r4_relat_2(C,A)
          & r1_tarski(B,A) )
       => r4_relat_2(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_orders_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_orders_2(B,A)
          <=> r7_relat_2(u1_orders_2(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r7_relat_2(B,A)
      <=> ( r1_relat_2(B,A)
          & r6_relat_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_orders_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v4_orders_2(A)
      <=> r8_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_2)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r8_relat_2(C,A)
          & r1_tarski(B,A) )
       => r8_relat_2(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_orders_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r3_orders_1(A,B)
        <=> ( r1_relat_2(A,B)
            & r8_relat_2(A,B)
            & r4_relat_2(A,B)
            & r6_relat_2(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_orders_1)).

tff(c_48,plain,(
    ~ r3_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_54,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_12,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_129,plain,(
    ! [A_72] :
      ( m1_subset_1(u1_orders_2(A_72),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_72),u1_struct_0(A_72))))
      | ~ l1_orders_2(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_10,plain,(
    ! [B_12,A_10] :
      ( v1_relat_1(B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_10))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_132,plain,(
    ! [A_72] :
      ( v1_relat_1(u1_orders_2(A_72))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_72),u1_struct_0(A_72)))
      | ~ l1_orders_2(A_72) ) ),
    inference(resolution,[status(thm)],[c_129,c_10])).

tff(c_135,plain,(
    ! [A_72] :
      ( v1_relat_1(u1_orders_2(A_72))
      | ~ l1_orders_2(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_132])).

tff(c_56,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_24,plain,(
    ! [A_19] :
      ( r4_relat_2(u1_orders_2(A_19),u1_struct_0(A_19))
      | ~ v5_orders_2(A_19)
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_108,plain,(
    ! [C_61,A_62,B_63] :
      ( r2_hidden(C_61,A_62)
      | ~ r2_hidden(C_61,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_158,plain,(
    ! [A_81,B_82,A_83] :
      ( r2_hidden('#skF_1'(A_81,B_82),A_83)
      | ~ m1_subset_1(A_81,k1_zfmisc_1(A_83))
      | r1_tarski(A_81,B_82) ) ),
    inference(resolution,[status(thm)],[c_6,c_108])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_170,plain,(
    ! [A_84,A_85] :
      ( ~ m1_subset_1(A_84,k1_zfmisc_1(A_85))
      | r1_tarski(A_84,A_85) ) ),
    inference(resolution,[status(thm)],[c_158,c_4])).

tff(c_178,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_170])).

tff(c_44,plain,(
    ! [C_28,B_27,A_26] :
      ( r4_relat_2(C_28,B_27)
      | ~ r1_tarski(B_27,A_26)
      | ~ r4_relat_2(C_28,A_26)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_185,plain,(
    ! [C_86] :
      ( r4_relat_2(C_86,'#skF_3')
      | ~ r4_relat_2(C_86,u1_struct_0('#skF_2'))
      | ~ v1_relat_1(C_86) ) ),
    inference(resolution,[status(thm)],[c_178,c_44])).

tff(c_189,plain,
    ( r4_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | ~ v5_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_185])).

tff(c_196,plain,
    ( r4_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_189])).

tff(c_198,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_201,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_135,c_198])).

tff(c_205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_201])).

tff(c_207,plain,(
    v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_52,plain,(
    v6_orders_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_221,plain,(
    ! [A_88,B_89] :
      ( r7_relat_2(u1_orders_2(A_88),B_89)
      | ~ v6_orders_2(B_89,A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_orders_2(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_224,plain,
    ( r7_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ v6_orders_2('#skF_3','#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_221])).

tff(c_227,plain,(
    r7_relat_2(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_224])).

tff(c_42,plain,(
    ! [B_25,A_24] :
      ( r1_relat_2(B_25,A_24)
      | ~ r7_relat_2(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_230,plain,
    ( r1_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(resolution,[status(thm)],[c_227,c_42])).

tff(c_236,plain,(
    r1_relat_2(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_230])).

tff(c_206,plain,(
    r4_relat_2(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_40,plain,(
    ! [B_25,A_24] :
      ( r6_relat_2(B_25,A_24)
      | ~ r7_relat_2(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_233,plain,
    ( r6_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(resolution,[status(thm)],[c_227,c_40])).

tff(c_239,plain,(
    r6_relat_2(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_233])).

tff(c_58,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_20,plain,(
    ! [A_18] :
      ( r8_relat_2(u1_orders_2(A_18),u1_struct_0(A_18))
      | ~ v4_orders_2(A_18)
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_46,plain,(
    ! [C_31,B_30,A_29] :
      ( r8_relat_2(C_31,B_30)
      | ~ r1_tarski(B_30,A_29)
      | ~ r8_relat_2(C_31,A_29)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_208,plain,(
    ! [C_87] :
      ( r8_relat_2(C_87,'#skF_3')
      | ~ r8_relat_2(C_87,u1_struct_0('#skF_2'))
      | ~ v1_relat_1(C_87) ) ),
    inference(resolution,[status(thm)],[c_178,c_46])).

tff(c_212,plain,
    ( r8_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_208])).

tff(c_219,plain,(
    r8_relat_2(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58,c_207,c_212])).

tff(c_271,plain,(
    ! [A_99,B_100] :
      ( r3_orders_1(A_99,B_100)
      | ~ r6_relat_2(A_99,B_100)
      | ~ r4_relat_2(A_99,B_100)
      | ~ r8_relat_2(A_99,B_100)
      | ~ r1_relat_2(A_99,B_100)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_274,plain,
    ( r3_orders_1(u1_orders_2('#skF_2'),'#skF_3')
    | ~ r6_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ r4_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ r1_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(resolution,[status(thm)],[c_219,c_271])).

tff(c_283,plain,(
    r3_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_236,c_206,c_239,c_274])).

tff(c_285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_283])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:12:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.79  
% 3.26/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.79  %$ v6_orders_2 > r8_relat_2 > r7_relat_2 > r6_relat_2 > r4_relat_2 > r3_orders_1 > r2_hidden > r1_tarski > r1_relat_2 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_relat_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.26/1.79  
% 3.26/1.79  %Foreground sorts:
% 3.26/1.79  
% 3.26/1.79  
% 3.26/1.79  %Background operators:
% 3.26/1.79  
% 3.26/1.79  
% 3.26/1.79  %Foreground operators:
% 3.26/1.79  tff(r3_orders_1, type, r3_orders_1: ($i * $i) > $o).
% 3.26/1.79  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.26/1.79  tff(r4_relat_2, type, r4_relat_2: ($i * $i) > $o).
% 3.26/1.79  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.26/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.26/1.79  tff(r6_relat_2, type, r6_relat_2: ($i * $i) > $o).
% 3.26/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.79  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 3.26/1.79  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.79  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.79  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.26/1.79  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.26/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.26/1.79  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.26/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.26/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.26/1.79  tff(r7_relat_2, type, r7_relat_2: ($i * $i) > $o).
% 3.26/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.79  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.26/1.79  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.26/1.79  tff(r8_relat_2, type, r8_relat_2: ($i * $i) > $o).
% 3.26/1.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.26/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.26/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.26/1.79  
% 3.26/1.82  tff(f_129, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: ((v6_orders_2(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => r3_orders_1(u1_orders_2(A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t136_orders_2)).
% 3.26/1.82  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.26/1.82  tff(f_86, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 3.26/1.82  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.26/1.82  tff(f_69, axiom, (![A]: (l1_orders_2(A) => (v5_orders_2(A) <=> r4_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_orders_2)).
% 3.26/1.82  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.26/1.82  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.26/1.82  tff(f_102, axiom, (![A, B, C]: (v1_relat_1(C) => ((r4_relat_2(C, A) & r1_tarski(B, A)) => r4_relat_2(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_orders_1)).
% 3.26/1.82  tff(f_57, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_orders_2(B, A) <=> r7_relat_2(u1_orders_2(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_orders_2)).
% 3.26/1.82  tff(f_94, axiom, (![A, B]: (v1_relat_1(B) => (r7_relat_2(B, A) <=> (r1_relat_2(B, A) & r6_relat_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_orders_1)).
% 3.26/1.82  tff(f_63, axiom, (![A]: (l1_orders_2(A) => (v4_orders_2(A) <=> r8_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_orders_2)).
% 3.26/1.82  tff(f_110, axiom, (![A, B, C]: (v1_relat_1(C) => ((r8_relat_2(C, A) & r1_tarski(B, A)) => r8_relat_2(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_orders_1)).
% 3.26/1.82  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (r3_orders_1(A, B) <=> (((r1_relat_2(A, B) & r8_relat_2(A, B)) & r4_relat_2(A, B)) & r6_relat_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_orders_1)).
% 3.26/1.82  tff(c_48, plain, (~r3_orders_1(u1_orders_2('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.26/1.82  tff(c_54, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.26/1.82  tff(c_12, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.26/1.82  tff(c_129, plain, (![A_72]: (m1_subset_1(u1_orders_2(A_72), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_72), u1_struct_0(A_72)))) | ~l1_orders_2(A_72))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.26/1.82  tff(c_10, plain, (![B_12, A_10]: (v1_relat_1(B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_10)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.26/1.82  tff(c_132, plain, (![A_72]: (v1_relat_1(u1_orders_2(A_72)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_72), u1_struct_0(A_72))) | ~l1_orders_2(A_72))), inference(resolution, [status(thm)], [c_129, c_10])).
% 3.26/1.82  tff(c_135, plain, (![A_72]: (v1_relat_1(u1_orders_2(A_72)) | ~l1_orders_2(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_132])).
% 3.26/1.82  tff(c_56, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.26/1.82  tff(c_24, plain, (![A_19]: (r4_relat_2(u1_orders_2(A_19), u1_struct_0(A_19)) | ~v5_orders_2(A_19) | ~l1_orders_2(A_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.26/1.82  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.26/1.82  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.26/1.82  tff(c_108, plain, (![C_61, A_62, B_63]: (r2_hidden(C_61, A_62) | ~r2_hidden(C_61, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.26/1.82  tff(c_158, plain, (![A_81, B_82, A_83]: (r2_hidden('#skF_1'(A_81, B_82), A_83) | ~m1_subset_1(A_81, k1_zfmisc_1(A_83)) | r1_tarski(A_81, B_82))), inference(resolution, [status(thm)], [c_6, c_108])).
% 3.26/1.82  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.26/1.82  tff(c_170, plain, (![A_84, A_85]: (~m1_subset_1(A_84, k1_zfmisc_1(A_85)) | r1_tarski(A_84, A_85))), inference(resolution, [status(thm)], [c_158, c_4])).
% 3.26/1.82  tff(c_178, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_170])).
% 3.26/1.82  tff(c_44, plain, (![C_28, B_27, A_26]: (r4_relat_2(C_28, B_27) | ~r1_tarski(B_27, A_26) | ~r4_relat_2(C_28, A_26) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.26/1.82  tff(c_185, plain, (![C_86]: (r4_relat_2(C_86, '#skF_3') | ~r4_relat_2(C_86, u1_struct_0('#skF_2')) | ~v1_relat_1(C_86))), inference(resolution, [status(thm)], [c_178, c_44])).
% 3.26/1.82  tff(c_189, plain, (r4_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_2')) | ~v5_orders_2('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_24, c_185])).
% 3.26/1.82  tff(c_196, plain, (r4_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_189])).
% 3.26/1.82  tff(c_198, plain, (~v1_relat_1(u1_orders_2('#skF_2'))), inference(splitLeft, [status(thm)], [c_196])).
% 3.26/1.82  tff(c_201, plain, (~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_135, c_198])).
% 3.26/1.82  tff(c_205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_201])).
% 3.26/1.82  tff(c_207, plain, (v1_relat_1(u1_orders_2('#skF_2'))), inference(splitRight, [status(thm)], [c_196])).
% 3.26/1.82  tff(c_52, plain, (v6_orders_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.26/1.82  tff(c_221, plain, (![A_88, B_89]: (r7_relat_2(u1_orders_2(A_88), B_89) | ~v6_orders_2(B_89, A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_orders_2(A_88))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.26/1.82  tff(c_224, plain, (r7_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~v6_orders_2('#skF_3', '#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_50, c_221])).
% 3.26/1.82  tff(c_227, plain, (r7_relat_2(u1_orders_2('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_224])).
% 3.26/1.82  tff(c_42, plain, (![B_25, A_24]: (r1_relat_2(B_25, A_24) | ~r7_relat_2(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.26/1.82  tff(c_230, plain, (r1_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_227, c_42])).
% 3.26/1.82  tff(c_236, plain, (r1_relat_2(u1_orders_2('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_230])).
% 3.26/1.82  tff(c_206, plain, (r4_relat_2(u1_orders_2('#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_196])).
% 3.26/1.82  tff(c_40, plain, (![B_25, A_24]: (r6_relat_2(B_25, A_24) | ~r7_relat_2(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.26/1.82  tff(c_233, plain, (r6_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_227, c_40])).
% 3.26/1.82  tff(c_239, plain, (r6_relat_2(u1_orders_2('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_233])).
% 3.26/1.82  tff(c_58, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.26/1.82  tff(c_20, plain, (![A_18]: (r8_relat_2(u1_orders_2(A_18), u1_struct_0(A_18)) | ~v4_orders_2(A_18) | ~l1_orders_2(A_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.26/1.82  tff(c_46, plain, (![C_31, B_30, A_29]: (r8_relat_2(C_31, B_30) | ~r1_tarski(B_30, A_29) | ~r8_relat_2(C_31, A_29) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.26/1.82  tff(c_208, plain, (![C_87]: (r8_relat_2(C_87, '#skF_3') | ~r8_relat_2(C_87, u1_struct_0('#skF_2')) | ~v1_relat_1(C_87))), inference(resolution, [status(thm)], [c_178, c_46])).
% 3.26/1.82  tff(c_212, plain, (r8_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_2')) | ~v4_orders_2('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_20, c_208])).
% 3.26/1.82  tff(c_219, plain, (r8_relat_2(u1_orders_2('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_58, c_207, c_212])).
% 3.26/1.82  tff(c_271, plain, (![A_99, B_100]: (r3_orders_1(A_99, B_100) | ~r6_relat_2(A_99, B_100) | ~r4_relat_2(A_99, B_100) | ~r8_relat_2(A_99, B_100) | ~r1_relat_2(A_99, B_100) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.26/1.82  tff(c_274, plain, (r3_orders_1(u1_orders_2('#skF_2'), '#skF_3') | ~r6_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~r4_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~r1_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_219, c_271])).
% 3.26/1.82  tff(c_283, plain, (r3_orders_1(u1_orders_2('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_236, c_206, c_239, c_274])).
% 3.26/1.82  tff(c_285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_283])).
% 3.26/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.82  
% 3.26/1.82  Inference rules
% 3.26/1.82  ----------------------
% 3.26/1.82  #Ref     : 0
% 3.26/1.82  #Sup     : 43
% 3.26/1.82  #Fact    : 0
% 3.26/1.82  #Define  : 0
% 3.26/1.82  #Split   : 2
% 3.26/1.82  #Chain   : 0
% 3.26/1.82  #Close   : 0
% 3.26/1.82  
% 3.26/1.82  Ordering : KBO
% 3.26/1.82  
% 3.26/1.82  Simplification rules
% 3.26/1.82  ----------------------
% 3.26/1.82  #Subsume      : 1
% 3.26/1.82  #Demod        : 17
% 3.26/1.82  #Tautology    : 8
% 3.26/1.82  #SimpNegUnit  : 1
% 3.26/1.82  #BackRed      : 0
% 3.26/1.82  
% 3.26/1.82  #Partial instantiations: 0
% 3.26/1.82  #Strategies tried      : 1
% 3.26/1.82  
% 3.26/1.82  Timing (in seconds)
% 3.26/1.82  ----------------------
% 3.41/1.83  Preprocessing        : 0.50
% 3.41/1.83  Parsing              : 0.28
% 3.41/1.83  CNF conversion       : 0.04
% 3.41/1.83  Main loop            : 0.43
% 3.41/1.83  Inferencing          : 0.18
% 3.41/1.83  Reduction            : 0.11
% 3.41/1.83  Demodulation         : 0.08
% 3.41/1.83  BG Simplification    : 0.03
% 3.41/1.83  Subsumption          : 0.08
% 3.41/1.83  Abstraction          : 0.01
% 3.41/1.83  MUC search           : 0.00
% 3.41/1.83  Cooper               : 0.00
% 3.41/1.83  Total                : 0.99
% 3.41/1.83  Index Insertion      : 0.00
% 3.41/1.83  Index Deletion       : 0.00
% 3.41/1.83  Index Matching       : 0.00
% 3.41/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
