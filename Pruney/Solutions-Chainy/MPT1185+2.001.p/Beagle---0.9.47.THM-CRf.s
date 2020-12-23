%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:11 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 186 expanded)
%              Number of leaves         :   35 (  81 expanded)
%              Depth                    :   10
%              Number of atoms          :  126 ( 537 expanded)
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

tff(f_114,negated_conjecture,(
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

tff(f_71,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v5_orders_2(A)
      <=> r4_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_orders_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r4_relat_2(C,A)
          & r1_tarski(B,A) )
       => r4_relat_2(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_orders_1)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_orders_2(B,A)
          <=> r7_relat_2(u1_orders_2(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r7_relat_2(B,A)
      <=> ( r1_relat_2(B,A)
          & r6_relat_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_orders_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v4_orders_2(A)
      <=> r8_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_2)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r8_relat_2(C,A)
          & r1_tarski(B,A) )
       => r8_relat_2(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_orders_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r3_orders_1(A,B)
        <=> ( r1_relat_2(A,B)
            & r8_relat_2(A,B)
            & r4_relat_2(A,B)
            & r6_relat_2(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_orders_1)).

tff(c_42,plain,(
    ~ r3_orders_1(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_48,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_146,plain,(
    ! [A_62] :
      ( m1_subset_1(u1_orders_2(A_62),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_62),u1_struct_0(A_62))))
      | ~ l1_orders_2(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [C_5,A_3,B_4] :
      ( v1_relat_1(C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_155,plain,(
    ! [A_63] :
      ( v1_relat_1(u1_orders_2(A_63))
      | ~ l1_orders_2(A_63) ) ),
    inference(resolution,[status(thm)],[c_146,c_6])).

tff(c_50,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_18,plain,(
    ! [A_10] :
      ( r4_relat_2(u1_orders_2(A_10),u1_struct_0(A_10))
      | ~ v5_orders_2(A_10)
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_57,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_61,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_57])).

tff(c_109,plain,(
    ! [C_52,B_53,A_54] :
      ( r4_relat_2(C_52,B_53)
      | ~ r1_tarski(B_53,A_54)
      | ~ r4_relat_2(C_52,A_54)
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_117,plain,(
    ! [C_58] :
      ( r4_relat_2(C_58,'#skF_2')
      | ~ r4_relat_2(C_58,u1_struct_0('#skF_1'))
      | ~ v1_relat_1(C_58) ) ),
    inference(resolution,[status(thm)],[c_61,c_109])).

tff(c_121,plain,
    ( r4_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1'))
    | ~ v5_orders_2('#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_117])).

tff(c_128,plain,
    ( r4_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_121])).

tff(c_130,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_158,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_155,c_130])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_158])).

tff(c_164,plain,(
    v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_46,plain,(
    v6_orders_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_221,plain,(
    ! [A_76,B_77] :
      ( r7_relat_2(u1_orders_2(A_76),B_77)
      | ~ v6_orders_2(B_77,A_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_orders_2(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_228,plain,
    ( r7_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v6_orders_2('#skF_2','#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_221])).

tff(c_232,plain,(
    r7_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_228])).

tff(c_36,plain,(
    ! [B_16,A_15] :
      ( r1_relat_2(B_16,A_15)
      | ~ r7_relat_2(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_241,plain,
    ( r1_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_232,c_36])).

tff(c_250,plain,(
    r1_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_241])).

tff(c_163,plain,(
    r4_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_34,plain,(
    ! [B_16,A_15] :
      ( r6_relat_2(B_16,A_15)
      | ~ r7_relat_2(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_238,plain,
    ( r6_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_232,c_34])).

tff(c_247,plain,(
    r6_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_238])).

tff(c_52,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_14,plain,(
    ! [A_9] :
      ( r8_relat_2(u1_orders_2(A_9),u1_struct_0(A_9))
      | ~ v4_orders_2(A_9)
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_113,plain,(
    ! [C_55,B_56,A_57] :
      ( r8_relat_2(C_55,B_56)
      | ~ r1_tarski(B_56,A_57)
      | ~ r8_relat_2(C_55,A_57)
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_175,plain,(
    ! [C_66] :
      ( r8_relat_2(C_66,'#skF_2')
      | ~ r8_relat_2(C_66,u1_struct_0('#skF_1'))
      | ~ v1_relat_1(C_66) ) ),
    inference(resolution,[status(thm)],[c_61,c_113])).

tff(c_179,plain,
    ( r8_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1'))
    | ~ v4_orders_2('#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_175])).

tff(c_186,plain,(
    r8_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_164,c_179])).

tff(c_277,plain,(
    ! [A_86,B_87] :
      ( r3_orders_1(A_86,B_87)
      | ~ r6_relat_2(A_86,B_87)
      | ~ r4_relat_2(A_86,B_87)
      | ~ r8_relat_2(A_86,B_87)
      | ~ r1_relat_2(A_86,B_87)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_280,plain,
    ( r3_orders_1(u1_orders_2('#skF_1'),'#skF_2')
    | ~ r6_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ r4_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ r1_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_186,c_277])).

tff(c_289,plain,(
    r3_orders_1(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_250,c_163,c_247,c_280])).

tff(c_291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_289])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:09:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.28  
% 2.23/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.29  %$ v6_orders_2 > r8_relat_2 > r7_relat_2 > r6_relat_2 > r4_relat_2 > r3_orders_1 > r1_tarski > r1_relat_2 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_relat_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.23/1.29  
% 2.23/1.29  %Foreground sorts:
% 2.23/1.29  
% 2.23/1.29  
% 2.23/1.29  %Background operators:
% 2.23/1.29  
% 2.23/1.29  
% 2.23/1.29  %Foreground operators:
% 2.23/1.29  tff(r3_orders_1, type, r3_orders_1: ($i * $i) > $o).
% 2.23/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.23/1.29  tff(r4_relat_2, type, r4_relat_2: ($i * $i) > $o).
% 2.23/1.29  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.29  tff(r6_relat_2, type, r6_relat_2: ($i * $i) > $o).
% 2.23/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.29  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 2.23/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.29  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.23/1.29  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.23/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.29  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.23/1.29  tff(r7_relat_2, type, r7_relat_2: ($i * $i) > $o).
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.29  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.23/1.29  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.23/1.29  tff(r8_relat_2, type, r8_relat_2: ($i * $i) > $o).
% 2.23/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.23/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.29  
% 2.23/1.30  tff(f_114, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: ((v6_orders_2(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => r3_orders_1(u1_orders_2(A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t136_orders_2)).
% 2.23/1.30  tff(f_71, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 2.23/1.30  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.23/1.30  tff(f_54, axiom, (![A]: (l1_orders_2(A) => (v5_orders_2(A) <=> r4_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_orders_2)).
% 2.23/1.30  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.23/1.30  tff(f_87, axiom, (![A, B, C]: (v1_relat_1(C) => ((r4_relat_2(C, A) & r1_tarski(B, A)) => r4_relat_2(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_orders_1)).
% 2.23/1.30  tff(f_42, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_orders_2(B, A) <=> r7_relat_2(u1_orders_2(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_orders_2)).
% 2.23/1.30  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (r7_relat_2(B, A) <=> (r1_relat_2(B, A) & r6_relat_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_orders_1)).
% 2.23/1.30  tff(f_48, axiom, (![A]: (l1_orders_2(A) => (v4_orders_2(A) <=> r8_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_orders_2)).
% 2.23/1.30  tff(f_95, axiom, (![A, B, C]: (v1_relat_1(C) => ((r8_relat_2(C, A) & r1_tarski(B, A)) => r8_relat_2(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_orders_1)).
% 2.23/1.30  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (r3_orders_1(A, B) <=> (((r1_relat_2(A, B) & r8_relat_2(A, B)) & r4_relat_2(A, B)) & r6_relat_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_orders_1)).
% 2.23/1.30  tff(c_42, plain, (~r3_orders_1(u1_orders_2('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.23/1.30  tff(c_48, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.23/1.30  tff(c_146, plain, (![A_62]: (m1_subset_1(u1_orders_2(A_62), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_62), u1_struct_0(A_62)))) | ~l1_orders_2(A_62))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.23/1.30  tff(c_6, plain, (![C_5, A_3, B_4]: (v1_relat_1(C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.30  tff(c_155, plain, (![A_63]: (v1_relat_1(u1_orders_2(A_63)) | ~l1_orders_2(A_63))), inference(resolution, [status(thm)], [c_146, c_6])).
% 2.23/1.30  tff(c_50, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.23/1.30  tff(c_18, plain, (![A_10]: (r4_relat_2(u1_orders_2(A_10), u1_struct_0(A_10)) | ~v5_orders_2(A_10) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.23/1.30  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.23/1.30  tff(c_57, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.30  tff(c_61, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_57])).
% 2.23/1.30  tff(c_109, plain, (![C_52, B_53, A_54]: (r4_relat_2(C_52, B_53) | ~r1_tarski(B_53, A_54) | ~r4_relat_2(C_52, A_54) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.23/1.30  tff(c_117, plain, (![C_58]: (r4_relat_2(C_58, '#skF_2') | ~r4_relat_2(C_58, u1_struct_0('#skF_1')) | ~v1_relat_1(C_58))), inference(resolution, [status(thm)], [c_61, c_109])).
% 2.23/1.30  tff(c_121, plain, (r4_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1')) | ~v5_orders_2('#skF_1') | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_18, c_117])).
% 2.23/1.30  tff(c_128, plain, (r4_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_121])).
% 2.23/1.30  tff(c_130, plain, (~v1_relat_1(u1_orders_2('#skF_1'))), inference(splitLeft, [status(thm)], [c_128])).
% 2.23/1.30  tff(c_158, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_155, c_130])).
% 2.23/1.30  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_158])).
% 2.23/1.30  tff(c_164, plain, (v1_relat_1(u1_orders_2('#skF_1'))), inference(splitRight, [status(thm)], [c_128])).
% 2.23/1.30  tff(c_46, plain, (v6_orders_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.23/1.30  tff(c_221, plain, (![A_76, B_77]: (r7_relat_2(u1_orders_2(A_76), B_77) | ~v6_orders_2(B_77, A_76) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_orders_2(A_76))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.30  tff(c_228, plain, (r7_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v6_orders_2('#skF_2', '#skF_1') | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_44, c_221])).
% 2.23/1.30  tff(c_232, plain, (r7_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_228])).
% 2.23/1.30  tff(c_36, plain, (![B_16, A_15]: (r1_relat_2(B_16, A_15) | ~r7_relat_2(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.23/1.30  tff(c_241, plain, (r1_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_232, c_36])).
% 2.23/1.30  tff(c_250, plain, (r1_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_241])).
% 2.23/1.30  tff(c_163, plain, (r4_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_128])).
% 2.23/1.30  tff(c_34, plain, (![B_16, A_15]: (r6_relat_2(B_16, A_15) | ~r7_relat_2(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.23/1.30  tff(c_238, plain, (r6_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_232, c_34])).
% 2.23/1.30  tff(c_247, plain, (r6_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_238])).
% 2.23/1.30  tff(c_52, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.23/1.30  tff(c_14, plain, (![A_9]: (r8_relat_2(u1_orders_2(A_9), u1_struct_0(A_9)) | ~v4_orders_2(A_9) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.23/1.30  tff(c_113, plain, (![C_55, B_56, A_57]: (r8_relat_2(C_55, B_56) | ~r1_tarski(B_56, A_57) | ~r8_relat_2(C_55, A_57) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.23/1.30  tff(c_175, plain, (![C_66]: (r8_relat_2(C_66, '#skF_2') | ~r8_relat_2(C_66, u1_struct_0('#skF_1')) | ~v1_relat_1(C_66))), inference(resolution, [status(thm)], [c_61, c_113])).
% 2.23/1.30  tff(c_179, plain, (r8_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1')) | ~v4_orders_2('#skF_1') | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_14, c_175])).
% 2.23/1.30  tff(c_186, plain, (r8_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_164, c_179])).
% 2.23/1.30  tff(c_277, plain, (![A_86, B_87]: (r3_orders_1(A_86, B_87) | ~r6_relat_2(A_86, B_87) | ~r4_relat_2(A_86, B_87) | ~r8_relat_2(A_86, B_87) | ~r1_relat_2(A_86, B_87) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.23/1.30  tff(c_280, plain, (r3_orders_1(u1_orders_2('#skF_1'), '#skF_2') | ~r6_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~r4_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~r1_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_186, c_277])).
% 2.23/1.30  tff(c_289, plain, (r3_orders_1(u1_orders_2('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_250, c_163, c_247, c_280])).
% 2.23/1.30  tff(c_291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_289])).
% 2.23/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.30  
% 2.23/1.30  Inference rules
% 2.23/1.30  ----------------------
% 2.23/1.30  #Ref     : 0
% 2.23/1.30  #Sup     : 41
% 2.23/1.30  #Fact    : 0
% 2.23/1.30  #Define  : 0
% 2.23/1.30  #Split   : 1
% 2.23/1.30  #Chain   : 0
% 2.23/1.30  #Close   : 0
% 2.23/1.30  
% 2.23/1.30  Ordering : KBO
% 2.23/1.30  
% 2.23/1.30  Simplification rules
% 2.23/1.30  ----------------------
% 2.23/1.30  #Subsume      : 2
% 2.23/1.30  #Demod        : 21
% 2.23/1.30  #Tautology    : 8
% 2.23/1.30  #SimpNegUnit  : 1
% 2.23/1.30  #BackRed      : 0
% 2.23/1.30  
% 2.23/1.30  #Partial instantiations: 0
% 2.23/1.30  #Strategies tried      : 1
% 2.23/1.30  
% 2.23/1.30  Timing (in seconds)
% 2.23/1.30  ----------------------
% 2.23/1.31  Preprocessing        : 0.30
% 2.23/1.31  Parsing              : 0.17
% 2.23/1.31  CNF conversion       : 0.02
% 2.23/1.31  Main loop            : 0.23
% 2.23/1.31  Inferencing          : 0.10
% 2.23/1.31  Reduction            : 0.06
% 2.23/1.31  Demodulation         : 0.04
% 2.23/1.31  BG Simplification    : 0.01
% 2.23/1.31  Subsumption          : 0.04
% 2.23/1.31  Abstraction          : 0.01
% 2.23/1.31  MUC search           : 0.00
% 2.23/1.31  Cooper               : 0.00
% 2.23/1.31  Total                : 0.56
% 2.23/1.31  Index Insertion      : 0.00
% 2.23/1.31  Index Deletion       : 0.00
% 2.23/1.31  Index Matching       : 0.00
% 2.23/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
