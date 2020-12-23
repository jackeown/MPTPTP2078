%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1185+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:33 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.57s
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

tff(f_113,negated_conjecture,(
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

tff(f_66,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v5_orders_2(A)
      <=> r4_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_orders_2)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r4_relat_2(C,A)
          & r1_tarski(B,A) )
       => r4_relat_2(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_orders_1)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_orders_2(B,A)
          <=> r7_relat_2(u1_orders_2(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r7_relat_2(B,A)
      <=> ( r1_relat_2(B,A)
          & r6_relat_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_orders_1)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v4_orders_2(A)
      <=> r8_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_orders_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r8_relat_2(C,A)
          & r1_tarski(B,A) )
       => r8_relat_2(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_orders_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r3_orders_1(A,B)
        <=> ( r1_relat_2(A,B)
            & r8_relat_2(A,B)
            & r4_relat_2(A,B)
            & r6_relat_2(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_orders_1)).

tff(c_42,plain,(
    ~ r3_orders_1(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_48,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_146,plain,(
    ! [A_62] :
      ( m1_subset_1(u1_orders_2(A_62),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_62),u1_struct_0(A_62))))
      | ~ l1_orders_2(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_155,plain,(
    ! [A_63] :
      ( v1_relat_1(u1_orders_2(A_63))
      | ~ l1_orders_2(A_63) ) ),
    inference(resolution,[status(thm)],[c_146,c_2])).

tff(c_50,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_14,plain,(
    ! [A_8] :
      ( r4_relat_2(u1_orders_2(A_8),u1_struct_0(A_8))
      | ~ v5_orders_2(A_8)
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_57,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_61,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_57])).

tff(c_109,plain,(
    ! [C_52,B_53,A_54] :
      ( r4_relat_2(C_52,B_53)
      | ~ r1_tarski(B_53,A_54)
      | ~ r4_relat_2(C_52,A_54)
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

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
    inference(resolution,[status(thm)],[c_14,c_117])).

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
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_203,plain,(
    ! [A_72,B_73] :
      ( r7_relat_2(u1_orders_2(A_72),B_73)
      | ~ v6_orders_2(B_73,A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_orders_2(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_210,plain,
    ( r7_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v6_orders_2('#skF_2','#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_203])).

tff(c_214,plain,(
    r7_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_210])).

tff(c_36,plain,(
    ! [B_16,A_15] :
      ( r1_relat_2(B_16,A_15)
      | ~ r7_relat_2(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_220,plain,
    ( r1_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_214,c_36])).

tff(c_226,plain,(
    r1_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_220])).

tff(c_163,plain,(
    r4_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_34,plain,(
    ! [B_16,A_15] :
      ( r6_relat_2(B_16,A_15)
      | ~ r7_relat_2(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_217,plain,
    ( r6_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_214,c_34])).

tff(c_223,plain,(
    r6_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_217])).

tff(c_52,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_10,plain,(
    ! [A_7] :
      ( r8_relat_2(u1_orders_2(A_7),u1_struct_0(A_7))
      | ~ v4_orders_2(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_113,plain,(
    ! [C_55,B_56,A_57] :
      ( r8_relat_2(C_55,B_56)
      | ~ r1_tarski(B_56,A_57)
      | ~ r8_relat_2(C_55,A_57)
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

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
    inference(resolution,[status(thm)],[c_10,c_175])).

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
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_280,plain,
    ( r3_orders_1(u1_orders_2('#skF_1'),'#skF_2')
    | ~ r6_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ r4_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ r1_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_186,c_277])).

tff(c_289,plain,(
    r3_orders_1(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_226,c_163,c_223,c_280])).

tff(c_291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_289])).

%------------------------------------------------------------------------------
