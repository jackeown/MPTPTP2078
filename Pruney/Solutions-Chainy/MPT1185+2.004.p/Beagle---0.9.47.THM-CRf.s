%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:11 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 189 expanded)
%              Number of leaves         :   36 (  82 expanded)
%              Depth                    :   10
%              Number of atoms          :  133 ( 544 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r8_relat_2 > r7_relat_2 > r6_relat_2 > r4_relat_2 > r3_orders_1 > r1_tarski > r1_relat_2 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_relat_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(r6_relat_2,type,(
    r6_relat_2: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_relat_2,type,(
    r1_relat_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_orders_2)).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v5_orders_2(A)
      <=> r4_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_orders_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r4_relat_2(C,A)
          & r1_tarski(B,A) )
       => r4_relat_2(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_orders_1)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_orders_2(B,A)
          <=> r7_relat_2(u1_orders_2(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r7_relat_2(B,A)
      <=> ( r1_relat_2(B,A)
          & r6_relat_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_orders_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v4_orders_2(A)
      <=> r8_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_orders_2)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r8_relat_2(C,A)
          & r1_tarski(B,A) )
       => r8_relat_2(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_orders_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r3_orders_1(A,B)
        <=> ( r1_relat_2(A,B)
            & r8_relat_2(A,B)
            & r4_relat_2(A,B)
            & r6_relat_2(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_orders_1)).

tff(c_44,plain,(
    ~ r3_orders_1(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_50,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_157,plain,(
    ! [A_64] :
      ( m1_subset_1(u1_orders_2(A_64),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_64),u1_struct_0(A_64))))
      | ~ l1_orders_2(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_160,plain,(
    ! [A_64] :
      ( v1_relat_1(u1_orders_2(A_64))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_64),u1_struct_0(A_64)))
      | ~ l1_orders_2(A_64) ) ),
    inference(resolution,[status(thm)],[c_157,c_6])).

tff(c_168,plain,(
    ! [A_65] :
      ( v1_relat_1(u1_orders_2(A_65))
      | ~ l1_orders_2(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_160])).

tff(c_52,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_20,plain,(
    ! [A_12] :
      ( r4_relat_2(u1_orders_2(A_12),u1_struct_0(A_12))
      | ~ v5_orders_2(A_12)
      | ~ l1_orders_2(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_60,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | ~ m1_subset_1(A_28,k1_zfmisc_1(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_60])).

tff(c_120,plain,(
    ! [C_54,B_55,A_56] :
      ( r4_relat_2(C_54,B_55)
      | ~ r1_tarski(B_55,A_56)
      | ~ r4_relat_2(C_54,A_56)
      | ~ v1_relat_1(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_124,plain,(
    ! [C_57] :
      ( r4_relat_2(C_57,'#skF_2')
      | ~ r4_relat_2(C_57,u1_struct_0('#skF_1'))
      | ~ v1_relat_1(C_57) ) ),
    inference(resolution,[status(thm)],[c_64,c_120])).

tff(c_128,plain,
    ( r4_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1'))
    | ~ v5_orders_2('#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_124])).

tff(c_135,plain,
    ( r4_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_128])).

tff(c_138,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_171,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_168,c_138])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_171])).

tff(c_177,plain,(
    v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_48,plain,(
    v6_orders_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_208,plain,(
    ! [A_73,B_74] :
      ( r7_relat_2(u1_orders_2(A_73),B_74)
      | ~ v6_orders_2(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_orders_2(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_215,plain,
    ( r7_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v6_orders_2('#skF_2','#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_208])).

tff(c_219,plain,(
    r7_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_215])).

tff(c_38,plain,(
    ! [B_18,A_17] :
      ( r1_relat_2(B_18,A_17)
      | ~ r7_relat_2(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_225,plain,
    ( r1_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_219,c_38])).

tff(c_231,plain,(
    r1_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_225])).

tff(c_176,plain,(
    r4_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_36,plain,(
    ! [B_18,A_17] :
      ( r6_relat_2(B_18,A_17)
      | ~ r7_relat_2(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_222,plain,
    ( r6_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_219,c_36])).

tff(c_228,plain,(
    r6_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_222])).

tff(c_54,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_16,plain,(
    ! [A_11] :
      ( r8_relat_2(u1_orders_2(A_11),u1_struct_0(A_11))
      | ~ v4_orders_2(A_11)
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_178,plain,(
    ! [C_66,B_67,A_68] :
      ( r8_relat_2(C_66,B_67)
      | ~ r1_tarski(B_67,A_68)
      | ~ r8_relat_2(C_66,A_68)
      | ~ v1_relat_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_182,plain,(
    ! [C_69] :
      ( r8_relat_2(C_69,'#skF_2')
      | ~ r8_relat_2(C_69,u1_struct_0('#skF_1'))
      | ~ v1_relat_1(C_69) ) ),
    inference(resolution,[status(thm)],[c_64,c_178])).

tff(c_186,plain,
    ( r8_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1'))
    | ~ v4_orders_2('#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_182])).

tff(c_193,plain,(
    r8_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_177,c_186])).

tff(c_284,plain,(
    ! [A_84,B_85] :
      ( r3_orders_1(A_84,B_85)
      | ~ r6_relat_2(A_84,B_85)
      | ~ r4_relat_2(A_84,B_85)
      | ~ r8_relat_2(A_84,B_85)
      | ~ r1_relat_2(A_84,B_85)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_287,plain,
    ( r3_orders_1(u1_orders_2('#skF_1'),'#skF_2')
    | ~ r6_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ r4_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ r1_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_193,c_284])).

tff(c_296,plain,(
    r3_orders_1(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_231,c_176,c_228,c_287])).

tff(c_298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_296])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.27  
% 2.26/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.27  %$ v6_orders_2 > r8_relat_2 > r7_relat_2 > r6_relat_2 > r4_relat_2 > r3_orders_1 > r1_tarski > r1_relat_2 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_relat_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.26/1.27  
% 2.26/1.27  %Foreground sorts:
% 2.26/1.27  
% 2.26/1.27  
% 2.26/1.27  %Background operators:
% 2.26/1.27  
% 2.26/1.27  
% 2.26/1.27  %Foreground operators:
% 2.26/1.27  tff(r3_orders_1, type, r3_orders_1: ($i * $i) > $o).
% 2.26/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.26/1.27  tff(r4_relat_2, type, r4_relat_2: ($i * $i) > $o).
% 2.26/1.27  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.26/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.27  tff(r6_relat_2, type, r6_relat_2: ($i * $i) > $o).
% 2.26/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.27  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 2.26/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.27  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.26/1.27  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.26/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.27  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.26/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.26/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.26/1.27  tff(r7_relat_2, type, r7_relat_2: ($i * $i) > $o).
% 2.26/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.27  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.26/1.27  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.26/1.27  tff(r8_relat_2, type, r8_relat_2: ($i * $i) > $o).
% 2.26/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.26/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.27  
% 2.26/1.29  tff(f_119, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: ((v6_orders_2(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => r3_orders_1(u1_orders_2(A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t136_orders_2)).
% 2.26/1.29  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.26/1.29  tff(f_76, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 2.26/1.29  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.26/1.29  tff(f_59, axiom, (![A]: (l1_orders_2(A) => (v5_orders_2(A) <=> r4_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_orders_2)).
% 2.26/1.29  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.26/1.29  tff(f_92, axiom, (![A, B, C]: (v1_relat_1(C) => ((r4_relat_2(C, A) & r1_tarski(B, A)) => r4_relat_2(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_orders_1)).
% 2.26/1.29  tff(f_47, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_orders_2(B, A) <=> r7_relat_2(u1_orders_2(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_orders_2)).
% 2.26/1.29  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => (r7_relat_2(B, A) <=> (r1_relat_2(B, A) & r6_relat_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_orders_1)).
% 2.26/1.29  tff(f_53, axiom, (![A]: (l1_orders_2(A) => (v4_orders_2(A) <=> r8_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_orders_2)).
% 2.26/1.29  tff(f_100, axiom, (![A, B, C]: (v1_relat_1(C) => ((r8_relat_2(C, A) & r1_tarski(B, A)) => r8_relat_2(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_orders_1)).
% 2.26/1.29  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (r3_orders_1(A, B) <=> (((r1_relat_2(A, B) & r8_relat_2(A, B)) & r4_relat_2(A, B)) & r6_relat_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_orders_1)).
% 2.26/1.29  tff(c_44, plain, (~r3_orders_1(u1_orders_2('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.26/1.29  tff(c_50, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.26/1.29  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.26/1.29  tff(c_157, plain, (![A_64]: (m1_subset_1(u1_orders_2(A_64), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_64), u1_struct_0(A_64)))) | ~l1_orders_2(A_64))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.26/1.29  tff(c_6, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.26/1.29  tff(c_160, plain, (![A_64]: (v1_relat_1(u1_orders_2(A_64)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_64), u1_struct_0(A_64))) | ~l1_orders_2(A_64))), inference(resolution, [status(thm)], [c_157, c_6])).
% 2.26/1.29  tff(c_168, plain, (![A_65]: (v1_relat_1(u1_orders_2(A_65)) | ~l1_orders_2(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_160])).
% 2.26/1.29  tff(c_52, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.26/1.29  tff(c_20, plain, (![A_12]: (r4_relat_2(u1_orders_2(A_12), u1_struct_0(A_12)) | ~v5_orders_2(A_12) | ~l1_orders_2(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.26/1.29  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.26/1.29  tff(c_60, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | ~m1_subset_1(A_28, k1_zfmisc_1(B_29)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.26/1.29  tff(c_64, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_60])).
% 2.26/1.29  tff(c_120, plain, (![C_54, B_55, A_56]: (r4_relat_2(C_54, B_55) | ~r1_tarski(B_55, A_56) | ~r4_relat_2(C_54, A_56) | ~v1_relat_1(C_54))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.26/1.29  tff(c_124, plain, (![C_57]: (r4_relat_2(C_57, '#skF_2') | ~r4_relat_2(C_57, u1_struct_0('#skF_1')) | ~v1_relat_1(C_57))), inference(resolution, [status(thm)], [c_64, c_120])).
% 2.26/1.29  tff(c_128, plain, (r4_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1')) | ~v5_orders_2('#skF_1') | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_20, c_124])).
% 2.26/1.29  tff(c_135, plain, (r4_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_128])).
% 2.26/1.29  tff(c_138, plain, (~v1_relat_1(u1_orders_2('#skF_1'))), inference(splitLeft, [status(thm)], [c_135])).
% 2.26/1.29  tff(c_171, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_168, c_138])).
% 2.26/1.29  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_171])).
% 2.26/1.29  tff(c_177, plain, (v1_relat_1(u1_orders_2('#skF_1'))), inference(splitRight, [status(thm)], [c_135])).
% 2.26/1.29  tff(c_48, plain, (v6_orders_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.26/1.29  tff(c_208, plain, (![A_73, B_74]: (r7_relat_2(u1_orders_2(A_73), B_74) | ~v6_orders_2(B_74, A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_orders_2(A_73))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.26/1.29  tff(c_215, plain, (r7_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v6_orders_2('#skF_2', '#skF_1') | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_46, c_208])).
% 2.26/1.29  tff(c_219, plain, (r7_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_215])).
% 2.26/1.29  tff(c_38, plain, (![B_18, A_17]: (r1_relat_2(B_18, A_17) | ~r7_relat_2(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.26/1.29  tff(c_225, plain, (r1_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_219, c_38])).
% 2.26/1.29  tff(c_231, plain, (r1_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_225])).
% 2.26/1.29  tff(c_176, plain, (r4_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_135])).
% 2.26/1.29  tff(c_36, plain, (![B_18, A_17]: (r6_relat_2(B_18, A_17) | ~r7_relat_2(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.26/1.29  tff(c_222, plain, (r6_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_219, c_36])).
% 2.26/1.29  tff(c_228, plain, (r6_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_222])).
% 2.26/1.29  tff(c_54, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.26/1.29  tff(c_16, plain, (![A_11]: (r8_relat_2(u1_orders_2(A_11), u1_struct_0(A_11)) | ~v4_orders_2(A_11) | ~l1_orders_2(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.26/1.29  tff(c_178, plain, (![C_66, B_67, A_68]: (r8_relat_2(C_66, B_67) | ~r1_tarski(B_67, A_68) | ~r8_relat_2(C_66, A_68) | ~v1_relat_1(C_66))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.26/1.29  tff(c_182, plain, (![C_69]: (r8_relat_2(C_69, '#skF_2') | ~r8_relat_2(C_69, u1_struct_0('#skF_1')) | ~v1_relat_1(C_69))), inference(resolution, [status(thm)], [c_64, c_178])).
% 2.26/1.29  tff(c_186, plain, (r8_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1')) | ~v4_orders_2('#skF_1') | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_16, c_182])).
% 2.26/1.29  tff(c_193, plain, (r8_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_177, c_186])).
% 2.26/1.29  tff(c_284, plain, (![A_84, B_85]: (r3_orders_1(A_84, B_85) | ~r6_relat_2(A_84, B_85) | ~r4_relat_2(A_84, B_85) | ~r8_relat_2(A_84, B_85) | ~r1_relat_2(A_84, B_85) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.26/1.29  tff(c_287, plain, (r3_orders_1(u1_orders_2('#skF_1'), '#skF_2') | ~r6_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~r4_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~r1_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_193, c_284])).
% 2.26/1.29  tff(c_296, plain, (r3_orders_1(u1_orders_2('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_231, c_176, c_228, c_287])).
% 2.26/1.29  tff(c_298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_296])).
% 2.26/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.29  
% 2.26/1.29  Inference rules
% 2.26/1.29  ----------------------
% 2.26/1.29  #Ref     : 0
% 2.26/1.29  #Sup     : 42
% 2.26/1.29  #Fact    : 0
% 2.26/1.29  #Define  : 0
% 2.26/1.29  #Split   : 2
% 2.26/1.29  #Chain   : 0
% 2.26/1.29  #Close   : 0
% 2.26/1.29  
% 2.26/1.29  Ordering : KBO
% 2.26/1.29  
% 2.26/1.29  Simplification rules
% 2.26/1.29  ----------------------
% 2.26/1.29  #Subsume      : 3
% 2.26/1.29  #Demod        : 25
% 2.26/1.29  #Tautology    : 8
% 2.26/1.29  #SimpNegUnit  : 1
% 2.26/1.29  #BackRed      : 0
% 2.26/1.29  
% 2.26/1.29  #Partial instantiations: 0
% 2.26/1.29  #Strategies tried      : 1
% 2.26/1.29  
% 2.26/1.29  Timing (in seconds)
% 2.26/1.29  ----------------------
% 2.26/1.29  Preprocessing        : 0.30
% 2.26/1.29  Parsing              : 0.17
% 2.26/1.29  CNF conversion       : 0.02
% 2.26/1.29  Main loop            : 0.23
% 2.26/1.29  Inferencing          : 0.09
% 2.26/1.29  Reduction            : 0.06
% 2.26/1.29  Demodulation         : 0.04
% 2.26/1.29  BG Simplification    : 0.01
% 2.26/1.29  Subsumption          : 0.03
% 2.26/1.29  Abstraction          : 0.01
% 2.26/1.29  MUC search           : 0.00
% 2.26/1.29  Cooper               : 0.00
% 2.26/1.29  Total                : 0.56
% 2.26/1.29  Index Insertion      : 0.00
% 2.26/1.29  Index Deletion       : 0.00
% 2.26/1.29  Index Matching       : 0.00
% 2.26/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
