%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:26 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 182 expanded)
%              Number of leaves         :   32 (  78 expanded)
%              Depth                    :   14
%              Number of atoms          :  120 ( 406 expanded)
%              Number of equality atoms :   22 (  73 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(c_34,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_40,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_38,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_47,plain,(
    ! [A_47] :
      ( k1_xboole_0 = A_47
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_38,c_47])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_59,plain,(
    ! [A_6] : r1_tarski('#skF_5',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_10])).

tff(c_109,plain,(
    ! [A_54,B_55] :
      ( k2_xboole_0(A_54,B_55) = B_55
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_113,plain,(
    ! [A_6] : k2_xboole_0('#skF_5',A_6) = A_6 ),
    inference(resolution,[status(thm)],[c_59,c_109])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_58,plain,(
    ! [A_12] : m1_subset_1('#skF_5',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_16])).

tff(c_218,plain,(
    ! [A_72,B_73] :
      ( r1_tarski('#skF_3'(A_72,B_73),B_73)
      | v2_tex_2(B_73,A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_228,plain,(
    ! [A_75] :
      ( r1_tarski('#skF_3'(A_75,'#skF_5'),'#skF_5')
      | v2_tex_2('#skF_5',A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_58,c_218])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_231,plain,(
    ! [A_75] :
      ( k2_xboole_0('#skF_3'(A_75,'#skF_5'),'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_228,c_8])).

tff(c_234,plain,(
    ! [A_76] :
      ( '#skF_3'(A_76,'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_2,c_231])).

tff(c_237,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_234,c_34])).

tff(c_240,plain,(
    '#skF_3'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_237])).

tff(c_42,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_252,plain,(
    ! [A_78,B_79] :
      ( m1_subset_1('#skF_3'(A_78,B_79),k1_zfmisc_1(u1_struct_0(A_78)))
      | v2_tex_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20,plain,(
    ! [B_18,A_16] :
      ( v4_pre_topc(B_18,A_16)
      | ~ v1_xboole_0(B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_281,plain,(
    ! [A_84,B_85] :
      ( v4_pre_topc('#skF_3'(A_84,B_85),A_84)
      | ~ v1_xboole_0('#skF_3'(A_84,B_85))
      | ~ v2_pre_topc(A_84)
      | v2_tex_2(B_85,A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_252,c_20])).

tff(c_307,plain,(
    ! [A_89] :
      ( v4_pre_topc('#skF_3'(A_89,'#skF_5'),A_89)
      | ~ v1_xboole_0('#skF_3'(A_89,'#skF_5'))
      | ~ v2_pre_topc(A_89)
      | v2_tex_2('#skF_5',A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_58,c_281])).

tff(c_310,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | ~ v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_4')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_307])).

tff(c_312,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_38,c_240,c_310])).

tff(c_313,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_312])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1('#skF_1'(A_7),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_174,plain,(
    ! [A_58,B_59,C_60] :
      ( k9_subset_1(A_58,B_59,B_59) = B_59
      | ~ m1_subset_1(C_60,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_180,plain,(
    ! [A_58,B_59] : k9_subset_1(A_58,B_59,B_59) = B_59 ),
    inference(resolution,[status(thm)],[c_12,c_174])).

tff(c_382,plain,(
    ! [A_102,B_103,D_104] :
      ( k9_subset_1(u1_struct_0(A_102),B_103,D_104) != '#skF_3'(A_102,B_103)
      | ~ v4_pre_topc(D_104,A_102)
      | ~ m1_subset_1(D_104,k1_zfmisc_1(u1_struct_0(A_102)))
      | v2_tex_2(B_103,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_386,plain,(
    ! [A_105,B_106] :
      ( '#skF_3'(A_105,B_106) != B_106
      | ~ v4_pre_topc(B_106,A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | v2_tex_2(B_106,A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_382])).

tff(c_393,plain,(
    ! [A_105] :
      ( '#skF_3'(A_105,'#skF_5') != '#skF_5'
      | ~ v4_pre_topc('#skF_5',A_105)
      | v2_tex_2('#skF_5',A_105)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(resolution,[status(thm)],[c_58,c_386])).

tff(c_405,plain,(
    ! [A_107] :
      ( '#skF_3'(A_107,'#skF_5') != '#skF_5'
      | ~ v4_pre_topc('#skF_5',A_107)
      | v2_tex_2('#skF_5',A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_393])).

tff(c_408,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_313,c_405])).

tff(c_414,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_240,c_408])).

tff(c_416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_414])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.36  
% 2.54/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.36  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.54/1.36  
% 2.54/1.36  %Foreground sorts:
% 2.54/1.36  
% 2.54/1.36  
% 2.54/1.36  %Background operators:
% 2.54/1.36  
% 2.54/1.36  
% 2.54/1.36  %Foreground operators:
% 2.54/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.54/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.54/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.54/1.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.54/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.54/1.36  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.54/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.54/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.54/1.36  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.54/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.54/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.54/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.54/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.54/1.36  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.54/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.54/1.36  
% 2.66/1.38  tff(f_100, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.66/1.38  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.66/1.38  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.66/1.38  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.66/1.38  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.66/1.38  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.66/1.38  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 2.66/1.38  tff(f_64, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.66/1.38  tff(f_41, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.66/1.38  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 2.66/1.38  tff(c_34, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.66/1.38  tff(c_40, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.66/1.38  tff(c_38, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.66/1.38  tff(c_47, plain, (![A_47]: (k1_xboole_0=A_47 | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.66/1.38  tff(c_56, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_38, c_47])).
% 2.66/1.38  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.66/1.38  tff(c_59, plain, (![A_6]: (r1_tarski('#skF_5', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_10])).
% 2.66/1.38  tff(c_109, plain, (![A_54, B_55]: (k2_xboole_0(A_54, B_55)=B_55 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.66/1.38  tff(c_113, plain, (![A_6]: (k2_xboole_0('#skF_5', A_6)=A_6)), inference(resolution, [status(thm)], [c_59, c_109])).
% 2.66/1.38  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.66/1.38  tff(c_16, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.66/1.38  tff(c_58, plain, (![A_12]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_16])).
% 2.66/1.38  tff(c_218, plain, (![A_72, B_73]: (r1_tarski('#skF_3'(A_72, B_73), B_73) | v2_tex_2(B_73, A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.66/1.38  tff(c_228, plain, (![A_75]: (r1_tarski('#skF_3'(A_75, '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', A_75) | ~l1_pre_topc(A_75))), inference(resolution, [status(thm)], [c_58, c_218])).
% 2.66/1.38  tff(c_8, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.66/1.38  tff(c_231, plain, (![A_75]: (k2_xboole_0('#skF_3'(A_75, '#skF_5'), '#skF_5')='#skF_5' | v2_tex_2('#skF_5', A_75) | ~l1_pre_topc(A_75))), inference(resolution, [status(thm)], [c_228, c_8])).
% 2.66/1.38  tff(c_234, plain, (![A_76]: ('#skF_3'(A_76, '#skF_5')='#skF_5' | v2_tex_2('#skF_5', A_76) | ~l1_pre_topc(A_76))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_2, c_231])).
% 2.66/1.38  tff(c_237, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_234, c_34])).
% 2.66/1.38  tff(c_240, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_237])).
% 2.66/1.38  tff(c_42, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.66/1.38  tff(c_252, plain, (![A_78, B_79]: (m1_subset_1('#skF_3'(A_78, B_79), k1_zfmisc_1(u1_struct_0(A_78))) | v2_tex_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.66/1.38  tff(c_20, plain, (![B_18, A_16]: (v4_pre_topc(B_18, A_16) | ~v1_xboole_0(B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.66/1.38  tff(c_281, plain, (![A_84, B_85]: (v4_pre_topc('#skF_3'(A_84, B_85), A_84) | ~v1_xboole_0('#skF_3'(A_84, B_85)) | ~v2_pre_topc(A_84) | v2_tex_2(B_85, A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_252, c_20])).
% 2.66/1.38  tff(c_307, plain, (![A_89]: (v4_pre_topc('#skF_3'(A_89, '#skF_5'), A_89) | ~v1_xboole_0('#skF_3'(A_89, '#skF_5')) | ~v2_pre_topc(A_89) | v2_tex_2('#skF_5', A_89) | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_58, c_281])).
% 2.66/1.38  tff(c_310, plain, (v4_pre_topc('#skF_5', '#skF_4') | ~v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_4') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_240, c_307])).
% 2.66/1.38  tff(c_312, plain, (v4_pre_topc('#skF_5', '#skF_4') | v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_38, c_240, c_310])).
% 2.66/1.38  tff(c_313, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_312])).
% 2.66/1.38  tff(c_12, plain, (![A_7]: (m1_subset_1('#skF_1'(A_7), A_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.66/1.38  tff(c_174, plain, (![A_58, B_59, C_60]: (k9_subset_1(A_58, B_59, B_59)=B_59 | ~m1_subset_1(C_60, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.66/1.38  tff(c_180, plain, (![A_58, B_59]: (k9_subset_1(A_58, B_59, B_59)=B_59)), inference(resolution, [status(thm)], [c_12, c_174])).
% 2.66/1.38  tff(c_382, plain, (![A_102, B_103, D_104]: (k9_subset_1(u1_struct_0(A_102), B_103, D_104)!='#skF_3'(A_102, B_103) | ~v4_pre_topc(D_104, A_102) | ~m1_subset_1(D_104, k1_zfmisc_1(u1_struct_0(A_102))) | v2_tex_2(B_103, A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.66/1.38  tff(c_386, plain, (![A_105, B_106]: ('#skF_3'(A_105, B_106)!=B_106 | ~v4_pre_topc(B_106, A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | v2_tex_2(B_106, A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(superposition, [status(thm), theory('equality')], [c_180, c_382])).
% 2.66/1.38  tff(c_393, plain, (![A_105]: ('#skF_3'(A_105, '#skF_5')!='#skF_5' | ~v4_pre_topc('#skF_5', A_105) | v2_tex_2('#skF_5', A_105) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(resolution, [status(thm)], [c_58, c_386])).
% 2.66/1.38  tff(c_405, plain, (![A_107]: ('#skF_3'(A_107, '#skF_5')!='#skF_5' | ~v4_pre_topc('#skF_5', A_107) | v2_tex_2('#skF_5', A_107) | ~l1_pre_topc(A_107))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_393])).
% 2.66/1.38  tff(c_408, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_313, c_405])).
% 2.66/1.38  tff(c_414, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_240, c_408])).
% 2.66/1.38  tff(c_416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_414])).
% 2.66/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.38  
% 2.66/1.38  Inference rules
% 2.66/1.38  ----------------------
% 2.66/1.38  #Ref     : 0
% 2.66/1.38  #Sup     : 78
% 2.66/1.38  #Fact    : 0
% 2.66/1.38  #Define  : 0
% 2.66/1.38  #Split   : 0
% 2.66/1.38  #Chain   : 0
% 2.66/1.38  #Close   : 0
% 2.66/1.38  
% 2.66/1.38  Ordering : KBO
% 2.66/1.38  
% 2.66/1.38  Simplification rules
% 2.66/1.38  ----------------------
% 2.66/1.38  #Subsume      : 3
% 2.66/1.38  #Demod        : 51
% 2.66/1.38  #Tautology    : 39
% 2.66/1.38  #SimpNegUnit  : 8
% 2.66/1.38  #BackRed      : 4
% 2.66/1.38  
% 2.66/1.38  #Partial instantiations: 0
% 2.66/1.38  #Strategies tried      : 1
% 2.66/1.38  
% 2.66/1.38  Timing (in seconds)
% 2.66/1.38  ----------------------
% 2.66/1.38  Preprocessing        : 0.31
% 2.66/1.38  Parsing              : 0.18
% 2.66/1.38  CNF conversion       : 0.02
% 2.66/1.38  Main loop            : 0.26
% 2.66/1.38  Inferencing          : 0.10
% 2.66/1.38  Reduction            : 0.08
% 2.66/1.38  Demodulation         : 0.06
% 2.66/1.38  BG Simplification    : 0.02
% 2.66/1.38  Subsumption          : 0.04
% 2.66/1.38  Abstraction          : 0.01
% 2.66/1.38  MUC search           : 0.00
% 2.66/1.38  Cooper               : 0.00
% 2.66/1.38  Total                : 0.60
% 2.66/1.38  Index Insertion      : 0.00
% 2.66/1.38  Index Deletion       : 0.00
% 2.66/1.38  Index Matching       : 0.00
% 2.66/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
