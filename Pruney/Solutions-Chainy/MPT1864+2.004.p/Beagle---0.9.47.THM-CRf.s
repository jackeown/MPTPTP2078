%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:14 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 104 expanded)
%              Number of leaves         :   33 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  149 ( 320 expanded)
%              Number of equality atoms :   17 (  34 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ ( r2_hidden(C,B)
                      & ! [D] :
                          ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( v3_pre_topc(D,A)
                              & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_90,axiom,(
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
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_48,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_170,plain,(
    ! [A_115,B_116,C_117] :
      ( r1_tarski(k2_tarski(A_115,B_116),C_117)
      | ~ r2_hidden(B_116,C_117)
      | ~ r2_hidden(A_115,C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_179,plain,(
    ! [A_1,C_117] :
      ( r1_tarski(k1_tarski(A_1),C_117)
      | ~ r2_hidden(A_1,C_117)
      | ~ r2_hidden(A_1,C_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_170])).

tff(c_66,plain,(
    ! [B_77,A_78] :
      ( v1_xboole_0(B_77)
      | ~ m1_subset_1(B_77,A_78)
      | ~ v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_74,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_66])).

tff(c_75,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_24,plain,(
    ! [B_33,A_32] :
      ( r2_hidden(B_33,A_32)
      | ~ m1_subset_1(B_33,A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_52,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_30,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(k1_tarski(A_34),k1_zfmisc_1(B_35))
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_264,plain,(
    ! [A_148,B_149,C_150] :
      ( v3_pre_topc('#skF_1'(A_148,B_149,C_150),A_148)
      | ~ r1_tarski(C_150,B_149)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ v2_tex_2(B_149,A_148)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_276,plain,(
    ! [A_148,B_149,A_34] :
      ( v3_pre_topc('#skF_1'(A_148,B_149,k1_tarski(A_34)),A_148)
      | ~ r1_tarski(k1_tarski(A_34),B_149)
      | ~ v2_tex_2(B_149,A_148)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148)
      | ~ r2_hidden(A_34,u1_struct_0(A_148)) ) ),
    inference(resolution,[status(thm)],[c_30,c_264])).

tff(c_471,plain,(
    ! [A_194,B_195,C_196] :
      ( k9_subset_1(u1_struct_0(A_194),B_195,'#skF_1'(A_194,B_195,C_196)) = C_196
      | ~ r1_tarski(C_196,B_195)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ v2_tex_2(B_195,A_194)
      | ~ m1_subset_1(B_195,k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ l1_pre_topc(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_622,plain,(
    ! [A_234,B_235,A_236] :
      ( k9_subset_1(u1_struct_0(A_234),B_235,'#skF_1'(A_234,B_235,k1_tarski(A_236))) = k1_tarski(A_236)
      | ~ r1_tarski(k1_tarski(A_236),B_235)
      | ~ v2_tex_2(B_235,A_234)
      | ~ m1_subset_1(B_235,k1_zfmisc_1(u1_struct_0(A_234)))
      | ~ l1_pre_topc(A_234)
      | ~ r2_hidden(A_236,u1_struct_0(A_234)) ) ),
    inference(resolution,[status(thm)],[c_30,c_471])).

tff(c_421,plain,(
    ! [A_188,B_189,C_190] :
      ( m1_subset_1('#skF_1'(A_188,B_189,C_190),k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ r1_tarski(C_190,B_189)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ v2_tex_2(B_189,A_188)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_46,plain,(
    ! [D_75] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',D_75) != k1_tarski('#skF_5')
      | ~ v3_pre_topc(D_75,'#skF_3')
      | ~ m1_subset_1(D_75,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_448,plain,(
    ! [B_189,C_190] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_189,C_190)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_189,C_190),'#skF_3')
      | ~ r1_tarski(C_190,B_189)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_189,'#skF_3')
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_421,c_46])).

tff(c_467,plain,(
    ! [B_189,C_190] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_189,C_190)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_189,C_190),'#skF_3')
      | ~ r1_tarski(C_190,B_189)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_189,'#skF_3')
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_448])).

tff(c_628,plain,(
    ! [A_236] :
      ( k1_tarski(A_236) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',k1_tarski(A_236)),'#skF_3')
      | ~ r1_tarski(k1_tarski(A_236),'#skF_4')
      | ~ m1_subset_1(k1_tarski(A_236),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(k1_tarski(A_236),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_236,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_467])).

tff(c_638,plain,(
    ! [A_237] :
      ( k1_tarski(A_237) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',k1_tarski(A_237)),'#skF_3')
      | ~ m1_subset_1(k1_tarski(A_237),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(k1_tarski(A_237),'#skF_4')
      | ~ r2_hidden(A_237,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_54,c_52,c_628])).

tff(c_649,plain,(
    ! [A_241] :
      ( k1_tarski(A_241) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',k1_tarski(A_241)),'#skF_3')
      | ~ r1_tarski(k1_tarski(A_241),'#skF_4')
      | ~ r2_hidden(A_241,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_30,c_638])).

tff(c_653,plain,(
    ! [A_34] :
      ( k1_tarski(A_34) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_34),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_34,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_276,c_649])).

tff(c_657,plain,(
    ! [A_242] :
      ( k1_tarski(A_242) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_242),'#skF_4')
      | ~ r2_hidden(A_242,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_653])).

tff(c_661,plain,(
    ! [B_33] :
      ( k1_tarski(B_33) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(B_33),'#skF_4')
      | ~ m1_subset_1(B_33,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_24,c_657])).

tff(c_665,plain,(
    ! [B_243] :
      ( k1_tarski(B_243) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(B_243),'#skF_4')
      | ~ m1_subset_1(B_243,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_661])).

tff(c_671,plain,(
    ! [A_244] :
      ( k1_tarski(A_244) != k1_tarski('#skF_5')
      | ~ m1_subset_1(A_244,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_244,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_179,c_665])).

tff(c_678,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_671])).

tff(c_683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_678])).

tff(c_685,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_750,plain,(
    ! [C_267,B_268,A_269] :
      ( ~ v1_xboole_0(C_267)
      | ~ m1_subset_1(B_268,k1_zfmisc_1(C_267))
      | ~ r2_hidden(A_269,B_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_757,plain,(
    ! [A_269] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_269,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_750])).

tff(c_762,plain,(
    ! [A_269] : ~ r2_hidden(A_269,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_757])).

tff(c_764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_762,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.50  
% 3.21/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.51  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.21/1.51  
% 3.21/1.51  %Foreground sorts:
% 3.21/1.51  
% 3.21/1.51  
% 3.21/1.51  %Background operators:
% 3.21/1.51  
% 3.21/1.51  
% 3.21/1.51  %Foreground operators:
% 3.21/1.51  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.21/1.51  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.21/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.21/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.21/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.21/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.21/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.21/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.21/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.21/1.51  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.21/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.21/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.21/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.21/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.21/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.21/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.21/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.21/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.21/1.51  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.21/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.51  
% 3.21/1.52  tff(f_112, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tex_2)).
% 3.21/1.52  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.21/1.52  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.21/1.52  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.21/1.52  tff(f_62, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 3.21/1.52  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 3.21/1.52  tff(f_69, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.21/1.52  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.21/1.52  tff(c_50, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.21/1.52  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.21/1.52  tff(c_170, plain, (![A_115, B_116, C_117]: (r1_tarski(k2_tarski(A_115, B_116), C_117) | ~r2_hidden(B_116, C_117) | ~r2_hidden(A_115, C_117))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.21/1.52  tff(c_179, plain, (![A_1, C_117]: (r1_tarski(k1_tarski(A_1), C_117) | ~r2_hidden(A_1, C_117) | ~r2_hidden(A_1, C_117))), inference(superposition, [status(thm), theory('equality')], [c_2, c_170])).
% 3.21/1.52  tff(c_66, plain, (![B_77, A_78]: (v1_xboole_0(B_77) | ~m1_subset_1(B_77, A_78) | ~v1_xboole_0(A_78))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.21/1.52  tff(c_74, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_66])).
% 3.21/1.52  tff(c_75, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_74])).
% 3.21/1.52  tff(c_24, plain, (![B_33, A_32]: (r2_hidden(B_33, A_32) | ~m1_subset_1(B_33, A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.21/1.52  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.21/1.52  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.21/1.52  tff(c_52, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.21/1.52  tff(c_30, plain, (![A_34, B_35]: (m1_subset_1(k1_tarski(A_34), k1_zfmisc_1(B_35)) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.21/1.52  tff(c_264, plain, (![A_148, B_149, C_150]: (v3_pre_topc('#skF_1'(A_148, B_149, C_150), A_148) | ~r1_tarski(C_150, B_149) | ~m1_subset_1(C_150, k1_zfmisc_1(u1_struct_0(A_148))) | ~v2_tex_2(B_149, A_148) | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.21/1.52  tff(c_276, plain, (![A_148, B_149, A_34]: (v3_pre_topc('#skF_1'(A_148, B_149, k1_tarski(A_34)), A_148) | ~r1_tarski(k1_tarski(A_34), B_149) | ~v2_tex_2(B_149, A_148) | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148) | ~r2_hidden(A_34, u1_struct_0(A_148)))), inference(resolution, [status(thm)], [c_30, c_264])).
% 3.21/1.52  tff(c_471, plain, (![A_194, B_195, C_196]: (k9_subset_1(u1_struct_0(A_194), B_195, '#skF_1'(A_194, B_195, C_196))=C_196 | ~r1_tarski(C_196, B_195) | ~m1_subset_1(C_196, k1_zfmisc_1(u1_struct_0(A_194))) | ~v2_tex_2(B_195, A_194) | ~m1_subset_1(B_195, k1_zfmisc_1(u1_struct_0(A_194))) | ~l1_pre_topc(A_194))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.21/1.52  tff(c_622, plain, (![A_234, B_235, A_236]: (k9_subset_1(u1_struct_0(A_234), B_235, '#skF_1'(A_234, B_235, k1_tarski(A_236)))=k1_tarski(A_236) | ~r1_tarski(k1_tarski(A_236), B_235) | ~v2_tex_2(B_235, A_234) | ~m1_subset_1(B_235, k1_zfmisc_1(u1_struct_0(A_234))) | ~l1_pre_topc(A_234) | ~r2_hidden(A_236, u1_struct_0(A_234)))), inference(resolution, [status(thm)], [c_30, c_471])).
% 3.21/1.52  tff(c_421, plain, (![A_188, B_189, C_190]: (m1_subset_1('#skF_1'(A_188, B_189, C_190), k1_zfmisc_1(u1_struct_0(A_188))) | ~r1_tarski(C_190, B_189) | ~m1_subset_1(C_190, k1_zfmisc_1(u1_struct_0(A_188))) | ~v2_tex_2(B_189, A_188) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.21/1.52  tff(c_46, plain, (![D_75]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', D_75)!=k1_tarski('#skF_5') | ~v3_pre_topc(D_75, '#skF_3') | ~m1_subset_1(D_75, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.21/1.52  tff(c_448, plain, (![B_189, C_190]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_189, C_190))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_189, C_190), '#skF_3') | ~r1_tarski(C_190, B_189) | ~m1_subset_1(C_190, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_189, '#skF_3') | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_421, c_46])).
% 3.21/1.52  tff(c_467, plain, (![B_189, C_190]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_189, C_190))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_189, C_190), '#skF_3') | ~r1_tarski(C_190, B_189) | ~m1_subset_1(C_190, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_189, '#skF_3') | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_448])).
% 3.21/1.52  tff(c_628, plain, (![A_236]: (k1_tarski(A_236)!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', k1_tarski(A_236)), '#skF_3') | ~r1_tarski(k1_tarski(A_236), '#skF_4') | ~m1_subset_1(k1_tarski(A_236), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(k1_tarski(A_236), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r2_hidden(A_236, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_622, c_467])).
% 3.21/1.52  tff(c_638, plain, (![A_237]: (k1_tarski(A_237)!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', k1_tarski(A_237)), '#skF_3') | ~m1_subset_1(k1_tarski(A_237), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(k1_tarski(A_237), '#skF_4') | ~r2_hidden(A_237, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_54, c_52, c_628])).
% 3.21/1.52  tff(c_649, plain, (![A_241]: (k1_tarski(A_241)!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', k1_tarski(A_241)), '#skF_3') | ~r1_tarski(k1_tarski(A_241), '#skF_4') | ~r2_hidden(A_241, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_30, c_638])).
% 3.21/1.52  tff(c_653, plain, (![A_34]: (k1_tarski(A_34)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_34), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r2_hidden(A_34, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_276, c_649])).
% 3.21/1.52  tff(c_657, plain, (![A_242]: (k1_tarski(A_242)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_242), '#skF_4') | ~r2_hidden(A_242, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_653])).
% 3.21/1.52  tff(c_661, plain, (![B_33]: (k1_tarski(B_33)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(B_33), '#skF_4') | ~m1_subset_1(B_33, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_24, c_657])).
% 3.21/1.52  tff(c_665, plain, (![B_243]: (k1_tarski(B_243)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(B_243), '#skF_4') | ~m1_subset_1(B_243, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_75, c_661])).
% 3.21/1.52  tff(c_671, plain, (![A_244]: (k1_tarski(A_244)!=k1_tarski('#skF_5') | ~m1_subset_1(A_244, u1_struct_0('#skF_3')) | ~r2_hidden(A_244, '#skF_4'))), inference(resolution, [status(thm)], [c_179, c_665])).
% 3.21/1.52  tff(c_678, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_671])).
% 3.21/1.52  tff(c_683, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_678])).
% 3.21/1.52  tff(c_685, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_74])).
% 3.21/1.52  tff(c_750, plain, (![C_267, B_268, A_269]: (~v1_xboole_0(C_267) | ~m1_subset_1(B_268, k1_zfmisc_1(C_267)) | ~r2_hidden(A_269, B_268))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.21/1.52  tff(c_757, plain, (![A_269]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_269, '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_750])).
% 3.21/1.52  tff(c_762, plain, (![A_269]: (~r2_hidden(A_269, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_685, c_757])).
% 3.21/1.52  tff(c_764, plain, $false, inference(negUnitSimplification, [status(thm)], [c_762, c_48])).
% 3.21/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.52  
% 3.21/1.52  Inference rules
% 3.21/1.52  ----------------------
% 3.21/1.52  #Ref     : 0
% 3.21/1.52  #Sup     : 145
% 3.21/1.52  #Fact    : 0
% 3.21/1.52  #Define  : 0
% 3.21/1.52  #Split   : 10
% 3.21/1.52  #Chain   : 0
% 3.21/1.52  #Close   : 0
% 3.21/1.52  
% 3.21/1.52  Ordering : KBO
% 3.21/1.52  
% 3.21/1.52  Simplification rules
% 3.21/1.52  ----------------------
% 3.21/1.52  #Subsume      : 22
% 3.21/1.52  #Demod        : 42
% 3.21/1.52  #Tautology    : 35
% 3.21/1.52  #SimpNegUnit  : 2
% 3.21/1.52  #BackRed      : 1
% 3.21/1.52  
% 3.21/1.52  #Partial instantiations: 0
% 3.21/1.52  #Strategies tried      : 1
% 3.21/1.52  
% 3.21/1.52  Timing (in seconds)
% 3.21/1.52  ----------------------
% 3.21/1.53  Preprocessing        : 0.34
% 3.21/1.53  Parsing              : 0.18
% 3.21/1.53  CNF conversion       : 0.03
% 3.21/1.53  Main loop            : 0.42
% 3.21/1.53  Inferencing          : 0.16
% 3.21/1.53  Reduction            : 0.11
% 3.21/1.53  Demodulation         : 0.08
% 3.21/1.53  BG Simplification    : 0.02
% 3.21/1.53  Subsumption          : 0.09
% 3.21/1.53  Abstraction          : 0.02
% 3.21/1.53  MUC search           : 0.00
% 3.21/1.53  Cooper               : 0.00
% 3.21/1.53  Total                : 0.79
% 3.21/1.53  Index Insertion      : 0.00
% 3.21/1.53  Index Deletion       : 0.00
% 3.21/1.53  Index Matching       : 0.00
% 3.21/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
