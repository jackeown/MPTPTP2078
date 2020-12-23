%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:49 EST 2020

% Result     : Theorem 13.90s
% Output     : CNFRefutation 13.90s
% Verified   : 
% Statistics : Number of formulae       :   77 (  92 expanded)
%              Number of leaves         :   40 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  123 ( 170 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v1_tops_2(B,A)
                 => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tops_2)).

tff(f_71,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_68,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v1_tops_2(C,A) )
               => v1_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k3_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(k5_xboole_0(A_8,C_10),B_9)
      | ~ r1_tarski(C_10,B_9)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_40,plain,(
    ! [A_46] : ~ v1_xboole_0(k1_zfmisc_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_114,plain,(
    ! [A_88,B_89] :
      ( r2_hidden(A_88,B_89)
      | v1_xboole_0(B_89)
      | ~ m1_subset_1(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    ! [C_45,A_41] :
      ( r1_tarski(C_45,A_41)
      | ~ r2_hidden(C_45,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_118,plain,(
    ! [A_88,A_41] :
      ( r1_tarski(A_88,A_41)
      | v1_xboole_0(k1_zfmisc_1(A_41))
      | ~ m1_subset_1(A_88,k1_zfmisc_1(A_41)) ) ),
    inference(resolution,[status(thm)],[c_114,c_28])).

tff(c_126,plain,(
    ! [A_90,A_91] :
      ( r1_tarski(A_90,A_91)
      | ~ m1_subset_1(A_90,k1_zfmisc_1(A_91)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_118])).

tff(c_138,plain,(
    r1_tarski('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_58,c_126])).

tff(c_154,plain,(
    ! [A_95,C_96,B_97] :
      ( r1_tarski(A_95,C_96)
      | ~ r1_tarski(B_97,C_96)
      | ~ r1_tarski(A_95,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_167,plain,(
    ! [A_98] :
      ( r1_tarski(A_98,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_98,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_138,c_154])).

tff(c_14,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_tarski(A_11,C_13)
      | ~ r1_tarski(B_12,C_13)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_277,plain,(
    ! [A_121,A_122] :
      ( r1_tarski(A_121,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_121,A_122)
      | ~ r1_tarski(A_122,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_167,c_14])).

tff(c_8234,plain,(
    ! [A_630,C_631,B_632] :
      ( r1_tarski(k5_xboole_0(A_630,C_631),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(B_632,'#skF_4')
      | ~ r1_tarski(C_631,B_632)
      | ~ r1_tarski(A_630,B_632) ) ),
    inference(resolution,[status(thm)],[c_12,c_277])).

tff(c_8312,plain,(
    ! [A_630,C_631] :
      ( r1_tarski(k5_xboole_0(A_630,C_631),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(C_631,'#skF_4')
      | ~ r1_tarski(A_630,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6,c_8234])).

tff(c_65,plain,(
    ! [C_71,A_72] :
      ( r2_hidden(C_71,k1_zfmisc_1(A_72))
      | ~ r1_tarski(C_71,A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_46,plain,(
    ! [A_52,B_53] :
      ( m1_subset_1(A_52,B_53)
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_69,plain,(
    ! [C_71,A_72] :
      ( m1_subset_1(C_71,k1_zfmisc_1(A_72))
      | ~ r1_tarski(C_71,A_72) ) ),
    inference(resolution,[status(thm)],[c_65,c_46])).

tff(c_60,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_54,plain,(
    v1_tops_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1300,plain,(
    ! [B_239,A_240,C_241] :
      ( v1_tops_2(B_239,A_240)
      | ~ v1_tops_2(C_241,A_240)
      | ~ r1_tarski(B_239,C_241)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_240))))
      | ~ m1_subset_1(B_239,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_240))))
      | ~ l1_pre_topc(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5435,plain,(
    ! [A_489,C_490,A_491,B_492] :
      ( v1_tops_2(k5_xboole_0(A_489,C_490),A_491)
      | ~ v1_tops_2(B_492,A_491)
      | ~ m1_subset_1(B_492,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_491))))
      | ~ m1_subset_1(k5_xboole_0(A_489,C_490),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_491))))
      | ~ l1_pre_topc(A_491)
      | ~ r1_tarski(C_490,B_492)
      | ~ r1_tarski(A_489,B_492) ) ),
    inference(resolution,[status(thm)],[c_12,c_1300])).

tff(c_5448,plain,(
    ! [A_489,C_490] :
      ( v1_tops_2(k5_xboole_0(A_489,C_490),'#skF_3')
      | ~ v1_tops_2('#skF_4','#skF_3')
      | ~ m1_subset_1(k5_xboole_0(A_489,C_490),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(C_490,'#skF_4')
      | ~ r1_tarski(A_489,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_5435])).

tff(c_5712,plain,(
    ! [A_510,C_511] :
      ( v1_tops_2(k5_xboole_0(A_510,C_511),'#skF_3')
      | ~ m1_subset_1(k5_xboole_0(A_510,C_511),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ r1_tarski(C_511,'#skF_4')
      | ~ r1_tarski(A_510,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_5448])).

tff(c_24268,plain,(
    ! [A_1158,C_1159] :
      ( v1_tops_2(k5_xboole_0(A_1158,C_1159),'#skF_3')
      | ~ r1_tarski(C_1159,'#skF_4')
      | ~ r1_tarski(A_1158,'#skF_4')
      | ~ r1_tarski(k5_xboole_0(A_1158,C_1159),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_69,c_5712])).

tff(c_24328,plain,(
    ! [A_1160,C_1161] :
      ( v1_tops_2(k5_xboole_0(A_1160,C_1161),'#skF_3')
      | ~ r1_tarski(C_1161,'#skF_4')
      | ~ r1_tarski(A_1160,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8312,c_24268])).

tff(c_24332,plain,(
    ! [A_1162,B_1163] :
      ( v1_tops_2(k4_xboole_0(A_1162,B_1163),'#skF_3')
      | ~ r1_tarski(k3_xboole_0(A_1162,B_1163),'#skF_4')
      | ~ r1_tarski(A_1162,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_24328])).

tff(c_182,plain,(
    ! [A_100,B_101,C_102] :
      ( k7_subset_1(A_100,B_101,C_102) = k4_xboole_0(B_101,C_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_191,plain,(
    ! [C_102] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_3')),'#skF_4',C_102) = k4_xboole_0('#skF_4',C_102) ),
    inference(resolution,[status(thm)],[c_58,c_182])).

tff(c_52,plain,(
    ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_3')),'#skF_4','#skF_5'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_201,plain,(
    ~ v1_tops_2(k4_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_52])).

tff(c_24335,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_24332,c_201])).

tff(c_24338,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_24335])).

tff(c_24341,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_24338])).

tff(c_24345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_24341])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:04:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.90/6.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.90/6.63  
% 13.90/6.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.90/6.64  %$ v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 13.90/6.64  
% 13.90/6.64  %Foreground sorts:
% 13.90/6.64  
% 13.90/6.64  
% 13.90/6.64  %Background operators:
% 13.90/6.64  
% 13.90/6.64  
% 13.90/6.64  %Foreground operators:
% 13.90/6.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.90/6.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.90/6.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.90/6.64  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 13.90/6.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 13.90/6.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.90/6.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.90/6.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.90/6.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.90/6.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.90/6.64  tff('#skF_5', type, '#skF_5': $i).
% 13.90/6.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.90/6.64  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 13.90/6.64  tff('#skF_3', type, '#skF_3': $i).
% 13.90/6.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.90/6.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.90/6.64  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 13.90/6.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.90/6.64  tff('#skF_4', type, '#skF_4': $i).
% 13.90/6.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.90/6.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.90/6.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.90/6.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 13.90/6.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.90/6.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.90/6.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.90/6.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.90/6.64  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 13.90/6.64  
% 13.90/6.65  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.90/6.65  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 13.90/6.65  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 13.90/6.65  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 13.90/6.65  tff(f_114, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tops_2)).
% 13.90/6.65  tff(f_71, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 13.90/6.65  tff(f_87, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 13.90/6.65  tff(f_68, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 13.90/6.65  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 13.90/6.65  tff(f_81, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 13.90/6.65  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tops_2)).
% 13.90/6.65  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 13.90/6.65  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.90/6.65  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(k3_xboole_0(A_5, C_7), B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.90/6.65  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.90/6.65  tff(c_12, plain, (![A_8, C_10, B_9]: (r1_tarski(k5_xboole_0(A_8, C_10), B_9) | ~r1_tarski(C_10, B_9) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.90/6.65  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 13.90/6.65  tff(c_40, plain, (![A_46]: (~v1_xboole_0(k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.90/6.65  tff(c_114, plain, (![A_88, B_89]: (r2_hidden(A_88, B_89) | v1_xboole_0(B_89) | ~m1_subset_1(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.90/6.65  tff(c_28, plain, (![C_45, A_41]: (r1_tarski(C_45, A_41) | ~r2_hidden(C_45, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.90/6.65  tff(c_118, plain, (![A_88, A_41]: (r1_tarski(A_88, A_41) | v1_xboole_0(k1_zfmisc_1(A_41)) | ~m1_subset_1(A_88, k1_zfmisc_1(A_41)))), inference(resolution, [status(thm)], [c_114, c_28])).
% 13.90/6.65  tff(c_126, plain, (![A_90, A_91]: (r1_tarski(A_90, A_91) | ~m1_subset_1(A_90, k1_zfmisc_1(A_91)))), inference(negUnitSimplification, [status(thm)], [c_40, c_118])).
% 13.90/6.65  tff(c_138, plain, (r1_tarski('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_58, c_126])).
% 13.90/6.65  tff(c_154, plain, (![A_95, C_96, B_97]: (r1_tarski(A_95, C_96) | ~r1_tarski(B_97, C_96) | ~r1_tarski(A_95, B_97))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.90/6.65  tff(c_167, plain, (![A_98]: (r1_tarski(A_98, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_98, '#skF_4'))), inference(resolution, [status(thm)], [c_138, c_154])).
% 13.90/6.65  tff(c_14, plain, (![A_11, C_13, B_12]: (r1_tarski(A_11, C_13) | ~r1_tarski(B_12, C_13) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.90/6.65  tff(c_277, plain, (![A_121, A_122]: (r1_tarski(A_121, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_121, A_122) | ~r1_tarski(A_122, '#skF_4'))), inference(resolution, [status(thm)], [c_167, c_14])).
% 13.90/6.65  tff(c_8234, plain, (![A_630, C_631, B_632]: (r1_tarski(k5_xboole_0(A_630, C_631), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(B_632, '#skF_4') | ~r1_tarski(C_631, B_632) | ~r1_tarski(A_630, B_632))), inference(resolution, [status(thm)], [c_12, c_277])).
% 13.90/6.65  tff(c_8312, plain, (![A_630, C_631]: (r1_tarski(k5_xboole_0(A_630, C_631), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(C_631, '#skF_4') | ~r1_tarski(A_630, '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_8234])).
% 13.90/6.65  tff(c_65, plain, (![C_71, A_72]: (r2_hidden(C_71, k1_zfmisc_1(A_72)) | ~r1_tarski(C_71, A_72))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.90/6.65  tff(c_46, plain, (![A_52, B_53]: (m1_subset_1(A_52, B_53) | ~r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.90/6.65  tff(c_69, plain, (![C_71, A_72]: (m1_subset_1(C_71, k1_zfmisc_1(A_72)) | ~r1_tarski(C_71, A_72))), inference(resolution, [status(thm)], [c_65, c_46])).
% 13.90/6.65  tff(c_60, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 13.90/6.65  tff(c_54, plain, (v1_tops_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 13.90/6.65  tff(c_1300, plain, (![B_239, A_240, C_241]: (v1_tops_2(B_239, A_240) | ~v1_tops_2(C_241, A_240) | ~r1_tarski(B_239, C_241) | ~m1_subset_1(C_241, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_240)))) | ~m1_subset_1(B_239, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_240)))) | ~l1_pre_topc(A_240))), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.90/6.65  tff(c_5435, plain, (![A_489, C_490, A_491, B_492]: (v1_tops_2(k5_xboole_0(A_489, C_490), A_491) | ~v1_tops_2(B_492, A_491) | ~m1_subset_1(B_492, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_491)))) | ~m1_subset_1(k5_xboole_0(A_489, C_490), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_491)))) | ~l1_pre_topc(A_491) | ~r1_tarski(C_490, B_492) | ~r1_tarski(A_489, B_492))), inference(resolution, [status(thm)], [c_12, c_1300])).
% 13.90/6.65  tff(c_5448, plain, (![A_489, C_490]: (v1_tops_2(k5_xboole_0(A_489, C_490), '#skF_3') | ~v1_tops_2('#skF_4', '#skF_3') | ~m1_subset_1(k5_xboole_0(A_489, C_490), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(C_490, '#skF_4') | ~r1_tarski(A_489, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_5435])).
% 13.90/6.65  tff(c_5712, plain, (![A_510, C_511]: (v1_tops_2(k5_xboole_0(A_510, C_511), '#skF_3') | ~m1_subset_1(k5_xboole_0(A_510, C_511), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~r1_tarski(C_511, '#skF_4') | ~r1_tarski(A_510, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_54, c_5448])).
% 13.90/6.65  tff(c_24268, plain, (![A_1158, C_1159]: (v1_tops_2(k5_xboole_0(A_1158, C_1159), '#skF_3') | ~r1_tarski(C_1159, '#skF_4') | ~r1_tarski(A_1158, '#skF_4') | ~r1_tarski(k5_xboole_0(A_1158, C_1159), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_69, c_5712])).
% 13.90/6.65  tff(c_24328, plain, (![A_1160, C_1161]: (v1_tops_2(k5_xboole_0(A_1160, C_1161), '#skF_3') | ~r1_tarski(C_1161, '#skF_4') | ~r1_tarski(A_1160, '#skF_4'))), inference(resolution, [status(thm)], [c_8312, c_24268])).
% 13.90/6.65  tff(c_24332, plain, (![A_1162, B_1163]: (v1_tops_2(k4_xboole_0(A_1162, B_1163), '#skF_3') | ~r1_tarski(k3_xboole_0(A_1162, B_1163), '#skF_4') | ~r1_tarski(A_1162, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_24328])).
% 13.90/6.65  tff(c_182, plain, (![A_100, B_101, C_102]: (k7_subset_1(A_100, B_101, C_102)=k4_xboole_0(B_101, C_102) | ~m1_subset_1(B_101, k1_zfmisc_1(A_100)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.90/6.65  tff(c_191, plain, (![C_102]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_3')), '#skF_4', C_102)=k4_xboole_0('#skF_4', C_102))), inference(resolution, [status(thm)], [c_58, c_182])).
% 13.90/6.65  tff(c_52, plain, (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_3')), '#skF_4', '#skF_5'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 13.90/6.65  tff(c_201, plain, (~v1_tops_2(k4_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_191, c_52])).
% 13.90/6.65  tff(c_24335, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_24332, c_201])).
% 13.90/6.65  tff(c_24338, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_24335])).
% 13.90/6.65  tff(c_24341, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_10, c_24338])).
% 13.90/6.65  tff(c_24345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_24341])).
% 13.90/6.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.90/6.65  
% 13.90/6.65  Inference rules
% 13.90/6.65  ----------------------
% 13.90/6.65  #Ref     : 0
% 13.90/6.65  #Sup     : 6056
% 13.90/6.65  #Fact    : 0
% 13.90/6.65  #Define  : 0
% 13.90/6.65  #Split   : 3
% 13.90/6.65  #Chain   : 0
% 13.90/6.65  #Close   : 0
% 13.90/6.65  
% 13.90/6.65  Ordering : KBO
% 13.90/6.65  
% 13.90/6.65  Simplification rules
% 13.90/6.65  ----------------------
% 13.90/6.65  #Subsume      : 283
% 13.90/6.65  #Demod        : 194
% 13.90/6.65  #Tautology    : 164
% 13.90/6.65  #SimpNegUnit  : 8
% 13.90/6.65  #BackRed      : 1
% 13.90/6.65  
% 13.90/6.65  #Partial instantiations: 0
% 13.90/6.65  #Strategies tried      : 1
% 13.90/6.65  
% 13.90/6.65  Timing (in seconds)
% 13.90/6.65  ----------------------
% 13.90/6.65  Preprocessing        : 0.34
% 13.90/6.65  Parsing              : 0.18
% 13.90/6.65  CNF conversion       : 0.02
% 13.90/6.65  Main loop            : 5.54
% 13.90/6.65  Inferencing          : 0.87
% 13.90/6.65  Reduction            : 1.36
% 13.90/6.65  Demodulation         : 1.05
% 13.90/6.65  BG Simplification    : 0.14
% 13.90/6.65  Subsumption          : 2.79
% 13.90/6.66  Abstraction          : 0.19
% 13.90/6.66  MUC search           : 0.00
% 13.90/6.66  Cooper               : 0.00
% 13.90/6.66  Total                : 5.92
% 13.90/6.66  Index Insertion      : 0.00
% 13.90/6.66  Index Deletion       : 0.00
% 13.90/6.66  Index Matching       : 0.00
% 13.90/6.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
