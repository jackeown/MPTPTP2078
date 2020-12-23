%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1873+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:36 EST 2020

% Result     : Theorem 55.44s
% Output     : CNFRefutation 55.44s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 552 expanded)
%              Number of leaves         :   33 ( 195 expanded)
%              Depth                    :   18
%              Number of atoms          :  339 (1816 expanded)
%              Number of equality atoms :   61 ( 300 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r1_tarski(C,B)
                   => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_30,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_57,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & r1_tarski(C,B) )
               => r1_tarski(k2_pre_topc(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_125813,plain,(
    ! [A_1040,B_1041,C_1042] :
      ( k9_subset_1(A_1040,B_1041,C_1042) = k3_xboole_0(B_1041,C_1042)
      | ~ m1_subset_1(C_1042,k1_zfmisc_1(A_1040)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_125819,plain,(
    ! [B_1041] : k9_subset_1(u1_struct_0('#skF_3'),B_1041,'#skF_4') = k3_xboole_0(B_1041,'#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_125813])).

tff(c_126085,plain,(
    ! [A_1051,C_1052,B_1053] :
      ( k9_subset_1(A_1051,C_1052,B_1053) = k9_subset_1(A_1051,B_1053,C_1052)
      | ~ m1_subset_1(C_1052,k1_zfmisc_1(A_1051)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_126089,plain,(
    ! [B_1053] : k9_subset_1(u1_struct_0('#skF_3'),B_1053,'#skF_4') = k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_1053) ),
    inference(resolution,[status(thm)],[c_40,c_126085])).

tff(c_126093,plain,(
    ! [B_1053] : k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_1053) = k3_xboole_0(B_1053,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125819,c_126089])).

tff(c_44,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_50,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_115,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_16,plain,(
    ! [A_8,B_22] :
      ( m1_subset_1('#skF_2'(A_8,B_22),k1_zfmisc_1(u1_struct_0(A_8)))
      | v2_tex_2(B_22,A_8)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1902,plain,(
    ! [A_135,B_136] :
      ( r1_tarski('#skF_2'(A_135,B_136),B_136)
      | v2_tex_2(B_136,A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1908,plain,
    ( r1_tarski('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1902])).

tff(c_1915,plain,
    ( r1_tarski('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1908])).

tff(c_1916,plain,(
    r1_tarski('#skF_2'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_1915])).

tff(c_602,plain,(
    ! [A_105,B_106,C_107] :
      ( k9_subset_1(A_105,B_106,C_107) = k3_xboole_0(B_106,C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_605,plain,(
    ! [B_106] : k9_subset_1(u1_struct_0('#skF_3'),B_106,'#skF_4') = k3_xboole_0(B_106,'#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_602])).

tff(c_1022,plain,(
    ! [A_117,C_118,B_119] :
      ( k9_subset_1(A_117,C_118,B_119) = k9_subset_1(A_117,B_119,C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(A_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1024,plain,(
    ! [B_119] : k9_subset_1(u1_struct_0('#skF_3'),B_119,'#skF_4') = k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_119) ),
    inference(resolution,[status(thm)],[c_40,c_1022])).

tff(c_1026,plain,(
    ! [B_119] : k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_119) = k3_xboole_0(B_119,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_1024])).

tff(c_62,plain,(
    ! [C_65] :
      ( v2_tex_2('#skF_4','#skF_3')
      | k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',C_65)) = C_65
      | ~ r1_tarski(C_65,'#skF_4')
      | ~ m1_subset_1(C_65,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_366,plain,(
    ! [C_65] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',C_65)) = C_65
      | ~ r1_tarski(C_65,'#skF_4')
      | ~ m1_subset_1(C_65,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_62])).

tff(c_1105,plain,(
    ! [C_65] :
      ( k3_xboole_0(k2_pre_topc('#skF_3',C_65),'#skF_4') = C_65
      | ~ r1_tarski(C_65,'#skF_4')
      | ~ m1_subset_1(C_65,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1026,c_366])).

tff(c_2825,plain,(
    ! [C_161] :
      ( k3_xboole_0('#skF_4',k2_pre_topc('#skF_3',C_161)) = C_161
      | ~ r1_tarski(C_161,'#skF_4')
      | ~ m1_subset_1(C_161,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1105])).

tff(c_2836,plain,(
    ! [B_22] :
      ( k3_xboole_0('#skF_4',k2_pre_topc('#skF_3','#skF_2'('#skF_3',B_22))) = '#skF_2'('#skF_3',B_22)
      | ~ r1_tarski('#skF_2'('#skF_3',B_22),'#skF_4')
      | v2_tex_2(B_22,'#skF_3')
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_2825])).

tff(c_29043,plain,(
    ! [B_475] :
      ( k3_xboole_0('#skF_4',k2_pre_topc('#skF_3','#skF_2'('#skF_3',B_475))) = '#skF_2'('#skF_3',B_475)
      | ~ r1_tarski('#skF_2'('#skF_3',B_475),'#skF_4')
      | v2_tex_2(B_475,'#skF_3')
      | ~ m1_subset_1(B_475,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2836])).

tff(c_29064,plain,
    ( k3_xboole_0('#skF_4',k2_pre_topc('#skF_3','#skF_2'('#skF_3','#skF_4'))) = '#skF_2'('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_29043])).

tff(c_29081,plain,
    ( k3_xboole_0('#skF_4',k2_pre_topc('#skF_3','#skF_2'('#skF_3','#skF_4'))) = '#skF_2'('#skF_3','#skF_4')
    | v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1916,c_29064])).

tff(c_29082,plain,(
    k3_xboole_0('#skF_4',k2_pre_topc('#skF_3','#skF_2'('#skF_3','#skF_4'))) = '#skF_2'('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_29081])).

tff(c_66,plain,(
    ! [B_69,A_70] : k3_xboole_0(B_69,A_70) = k3_xboole_0(A_70,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_30,plain,(
    ! [A_40,B_41] : r1_tarski(k3_xboole_0(A_40,B_41),A_40) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_81,plain,(
    ! [B_69,A_70] : r1_tarski(k3_xboole_0(B_69,A_70),A_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_30])).

tff(c_29342,plain,(
    r1_tarski('#skF_2'('#skF_3','#skF_4'),k2_pre_topc('#skF_3','#skF_2'('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_29082,c_81])).

tff(c_2152,plain,(
    ! [A_139,C_140,B_141] :
      ( r1_tarski(k2_pre_topc(A_139,C_140),B_141)
      | ~ r1_tarski(C_140,B_141)
      | ~ v4_pre_topc(B_141,A_139)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_pre_topc(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_9001,plain,(
    ! [A_265,B_266,B_267] :
      ( r1_tarski(k2_pre_topc(A_265,'#skF_2'(A_265,B_266)),B_267)
      | ~ r1_tarski('#skF_2'(A_265,B_266),B_267)
      | ~ v4_pre_topc(B_267,A_265)
      | ~ m1_subset_1(B_267,k1_zfmisc_1(u1_struct_0(A_265)))
      | v2_tex_2(B_266,A_265)
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ l1_pre_topc(A_265) ) ),
    inference(resolution,[status(thm)],[c_16,c_2152])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_45928,plain,(
    ! [A_596,B_597,B_598] :
      ( k2_pre_topc(A_596,'#skF_2'(A_596,B_597)) = B_598
      | ~ r1_tarski(B_598,k2_pre_topc(A_596,'#skF_2'(A_596,B_597)))
      | ~ r1_tarski('#skF_2'(A_596,B_597),B_598)
      | ~ v4_pre_topc(B_598,A_596)
      | ~ m1_subset_1(B_598,k1_zfmisc_1(u1_struct_0(A_596)))
      | v2_tex_2(B_597,A_596)
      | ~ m1_subset_1(B_597,k1_zfmisc_1(u1_struct_0(A_596)))
      | ~ l1_pre_topc(A_596) ) ),
    inference(resolution,[status(thm)],[c_9001,c_6])).

tff(c_45972,plain,
    ( k2_pre_topc('#skF_3','#skF_2'('#skF_3','#skF_4')) = '#skF_2'('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_2'('#skF_3','#skF_4'),'#skF_2'('#skF_3','#skF_4'))
    | ~ v4_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_29342,c_45928])).

tff(c_46103,plain,
    ( k2_pre_topc('#skF_3','#skF_2'('#skF_3','#skF_4')) = '#skF_2'('#skF_3','#skF_4')
    | ~ v4_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_10,c_45972])).

tff(c_46104,plain,
    ( k2_pre_topc('#skF_3','#skF_2'('#skF_3','#skF_4')) = '#skF_2'('#skF_3','#skF_4')
    | ~ v4_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_46103])).

tff(c_46312,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_46104])).

tff(c_46315,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_46312])).

tff(c_46318,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_46315])).

tff(c_46320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_46318])).

tff(c_46322,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_46104])).

tff(c_26,plain,(
    ! [A_35,B_36] :
      ( v4_pre_topc(k2_pre_topc(A_35,B_36),A_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_46385,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_3','#skF_2'('#skF_3','#skF_4')),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46322,c_26])).

tff(c_46465,plain,(
    v4_pre_topc(k2_pre_topc('#skF_3','#skF_2'('#skF_3','#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_46385])).

tff(c_24,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k2_pre_topc(A_33,B_34),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2670,plain,(
    ! [A_154,B_155,D_156] :
      ( k9_subset_1(u1_struct_0(A_154),B_155,D_156) != '#skF_2'(A_154,B_155)
      | ~ v4_pre_topc(D_156,A_154)
      | ~ m1_subset_1(D_156,k1_zfmisc_1(u1_struct_0(A_154)))
      | v2_tex_2(B_155,A_154)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2676,plain,(
    ! [B_119] :
      ( k3_xboole_0(B_119,'#skF_4') != '#skF_2'('#skF_3','#skF_4')
      | ~ v4_pre_topc(B_119,'#skF_3')
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1026,c_2670])).

tff(c_2686,plain,(
    ! [B_119] :
      ( k3_xboole_0(B_119,'#skF_4') != '#skF_2'('#skF_3','#skF_4')
      | ~ v4_pre_topc(B_119,'#skF_3')
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_2676])).

tff(c_2784,plain,(
    ! [B_160] :
      ( k3_xboole_0(B_160,'#skF_4') != '#skF_2'('#skF_3','#skF_4')
      | ~ v4_pre_topc(B_160,'#skF_3')
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_2686])).

tff(c_2799,plain,(
    ! [B_34] :
      ( k3_xboole_0(k2_pre_topc('#skF_3',B_34),'#skF_4') != '#skF_2'('#skF_3','#skF_4')
      | ~ v4_pre_topc(k2_pre_topc('#skF_3',B_34),'#skF_3')
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_2784])).

tff(c_125398,plain,(
    ! [B_1014] :
      ( k3_xboole_0('#skF_4',k2_pre_topc('#skF_3',B_1014)) != '#skF_2'('#skF_3','#skF_4')
      | ~ v4_pre_topc(k2_pre_topc('#skF_3',B_1014),'#skF_3')
      | ~ m1_subset_1(B_1014,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2,c_2799])).

tff(c_125401,plain,
    ( k3_xboole_0('#skF_4',k2_pre_topc('#skF_3','#skF_2'('#skF_3','#skF_4'))) != '#skF_2'('#skF_3','#skF_4')
    | ~ v4_pre_topc(k2_pre_topc('#skF_3','#skF_2'('#skF_3','#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_46322,c_125398])).

tff(c_125426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46465,c_29082,c_125401])).

tff(c_125428,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3','#skF_5')) != '#skF_5'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_125432,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3','#skF_5')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125428,c_48])).

tff(c_126123,plain,(
    k3_xboole_0(k2_pre_topc('#skF_3','#skF_5'),'#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126093,c_125432])).

tff(c_126124,plain,(
    k3_xboole_0('#skF_4',k2_pre_topc('#skF_3','#skF_5')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_126123])).

tff(c_52,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_125430,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125428,c_52])).

tff(c_125427,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_128066,plain,(
    ! [A_1091,B_1092,C_1093] :
      ( v4_pre_topc('#skF_1'(A_1091,B_1092,C_1093),A_1091)
      | ~ r1_tarski(C_1093,B_1092)
      | ~ m1_subset_1(C_1093,k1_zfmisc_1(u1_struct_0(A_1091)))
      | ~ v2_tex_2(B_1092,A_1091)
      | ~ m1_subset_1(B_1092,k1_zfmisc_1(u1_struct_0(A_1091)))
      | ~ l1_pre_topc(A_1091) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_128072,plain,(
    ! [B_1092] :
      ( v4_pre_topc('#skF_1'('#skF_3',B_1092,'#skF_5'),'#skF_3')
      | ~ r1_tarski('#skF_5',B_1092)
      | ~ v2_tex_2(B_1092,'#skF_3')
      | ~ m1_subset_1(B_1092,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_125430,c_128066])).

tff(c_130593,plain,(
    ! [B_1128] :
      ( v4_pre_topc('#skF_1'('#skF_3',B_1128,'#skF_5'),'#skF_3')
      | ~ r1_tarski('#skF_5',B_1128)
      | ~ v2_tex_2(B_1128,'#skF_3')
      | ~ m1_subset_1(B_1128,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_128072])).

tff(c_130611,plain,
    ( v4_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_130593])).

tff(c_130626,plain,(
    v4_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125428,c_125427,c_130611])).

tff(c_128698,plain,(
    ! [A_1107,B_1108,C_1109] :
      ( k9_subset_1(u1_struct_0(A_1107),B_1108,'#skF_1'(A_1107,B_1108,C_1109)) = C_1109
      | ~ r1_tarski(C_1109,B_1108)
      | ~ m1_subset_1(C_1109,k1_zfmisc_1(u1_struct_0(A_1107)))
      | ~ v2_tex_2(B_1108,A_1107)
      | ~ m1_subset_1(B_1108,k1_zfmisc_1(u1_struct_0(A_1107)))
      | ~ l1_pre_topc(A_1107) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_128706,plain,(
    ! [B_1108] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_1108,'#skF_1'('#skF_3',B_1108,'#skF_5')) = '#skF_5'
      | ~ r1_tarski('#skF_5',B_1108)
      | ~ v2_tex_2(B_1108,'#skF_3')
      | ~ m1_subset_1(B_1108,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_125430,c_128698])).

tff(c_131921,plain,(
    ! [B_1144] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_1144,'#skF_1'('#skF_3',B_1144,'#skF_5')) = '#skF_5'
      | ~ r1_tarski('#skF_5',B_1144)
      | ~ v2_tex_2(B_1144,'#skF_3')
      | ~ m1_subset_1(B_1144,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_128706])).

tff(c_131934,plain,
    ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_131921])).

tff(c_131949,plain,(
    k3_xboole_0('#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125428,c_125427,c_2,c_126093,c_131934])).

tff(c_132046,plain,(
    r1_tarski('#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_131949,c_81])).

tff(c_126487,plain,(
    ! [B_1063,A_1064] :
      ( r1_tarski(B_1063,k2_pre_topc(A_1064,B_1063))
      | ~ m1_subset_1(B_1063,k1_zfmisc_1(u1_struct_0(A_1064)))
      | ~ l1_pre_topc(A_1064) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_126489,plain,
    ( r1_tarski('#skF_5',k2_pre_topc('#skF_3','#skF_5'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_125430,c_126487])).

tff(c_126494,plain,(
    r1_tarski('#skF_5',k2_pre_topc('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_126489])).

tff(c_125560,plain,(
    ! [A_1034,B_1035,C_1036] :
      ( r1_tarski(A_1034,k3_xboole_0(B_1035,C_1036))
      | ~ r1_tarski(A_1034,C_1036)
      | ~ r1_tarski(A_1034,B_1035) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_125433,plain,(
    ! [B_1015,A_1016] :
      ( B_1015 = A_1016
      | ~ r1_tarski(B_1015,A_1016)
      | ~ r1_tarski(A_1016,B_1015) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_125444,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = A_40
      | ~ r1_tarski(A_40,k3_xboole_0(A_40,B_41)) ) ),
    inference(resolution,[status(thm)],[c_30,c_125433])).

tff(c_125576,plain,(
    ! [B_1035,C_1036] :
      ( k3_xboole_0(B_1035,C_1036) = B_1035
      | ~ r1_tarski(B_1035,C_1036)
      | ~ r1_tarski(B_1035,B_1035) ) ),
    inference(resolution,[status(thm)],[c_125560,c_125444])).

tff(c_125596,plain,(
    ! [B_1035,C_1036] :
      ( k3_xboole_0(B_1035,C_1036) = B_1035
      | ~ r1_tarski(B_1035,C_1036) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_125576])).

tff(c_126507,plain,(
    k3_xboole_0('#skF_5',k2_pre_topc('#skF_3','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_126494,c_125596])).

tff(c_22,plain,(
    ! [A_8,B_22,C_29] :
      ( m1_subset_1('#skF_1'(A_8,B_22,C_29),k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ r1_tarski(C_29,B_22)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ v2_tex_2(B_22,A_8)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_128017,plain,(
    ! [A_1087,C_1088,B_1089] :
      ( r1_tarski(k2_pre_topc(A_1087,C_1088),B_1089)
      | ~ r1_tarski(C_1088,B_1089)
      | ~ v4_pre_topc(B_1089,A_1087)
      | ~ m1_subset_1(C_1088,k1_zfmisc_1(u1_struct_0(A_1087)))
      | ~ m1_subset_1(B_1089,k1_zfmisc_1(u1_struct_0(A_1087)))
      | ~ l1_pre_topc(A_1087) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_128023,plain,(
    ! [B_1089] :
      ( r1_tarski(k2_pre_topc('#skF_3','#skF_5'),B_1089)
      | ~ r1_tarski('#skF_5',B_1089)
      | ~ v4_pre_topc(B_1089,'#skF_3')
      | ~ m1_subset_1(B_1089,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_125430,c_128017])).

tff(c_128662,plain,(
    ! [B_1106] :
      ( r1_tarski(k2_pre_topc('#skF_3','#skF_5'),B_1106)
      | ~ r1_tarski('#skF_5',B_1106)
      | ~ v4_pre_topc(B_1106,'#skF_3')
      | ~ m1_subset_1(B_1106,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_128023])).

tff(c_128666,plain,(
    ! [B_22,C_29] :
      ( r1_tarski(k2_pre_topc('#skF_3','#skF_5'),'#skF_1'('#skF_3',B_22,C_29))
      | ~ r1_tarski('#skF_5','#skF_1'('#skF_3',B_22,C_29))
      | ~ v4_pre_topc('#skF_1'('#skF_3',B_22,C_29),'#skF_3')
      | ~ r1_tarski(C_29,B_22)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_22,'#skF_3')
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_128662])).

tff(c_185914,plain,(
    ! [B_1506,C_1507] :
      ( r1_tarski(k2_pre_topc('#skF_3','#skF_5'),'#skF_1'('#skF_3',B_1506,C_1507))
      | ~ r1_tarski('#skF_5','#skF_1'('#skF_3',B_1506,C_1507))
      | ~ v4_pre_topc('#skF_1'('#skF_3',B_1506,C_1507),'#skF_3')
      | ~ r1_tarski(C_1507,B_1506)
      | ~ m1_subset_1(C_1507,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_1506,'#skF_3')
      | ~ m1_subset_1(B_1506,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_128666])).

tff(c_125464,plain,(
    ! [A_1021,C_1022,B_1023] :
      ( r1_tarski(k3_xboole_0(A_1021,C_1022),k3_xboole_0(B_1023,C_1022))
      | ~ r1_tarski(A_1021,B_1023) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_125533,plain,(
    ! [A_1031,B_1032,A_1033] :
      ( r1_tarski(k3_xboole_0(A_1031,B_1032),k3_xboole_0(B_1032,A_1033))
      | ~ r1_tarski(A_1031,A_1033) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_125464])).

tff(c_125552,plain,(
    ! [A_1,B_2,A_1033] :
      ( r1_tarski(k3_xboole_0(A_1,B_2),k3_xboole_0(A_1,A_1033))
      | ~ r1_tarski(B_2,A_1033) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_125533])).

tff(c_125479,plain,(
    ! [A_1,B_2,B_1023] :
      ( r1_tarski(k3_xboole_0(A_1,B_2),k3_xboole_0(B_1023,A_1))
      | ~ r1_tarski(B_2,B_1023) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_125464])).

tff(c_129000,plain,(
    ! [B_1111,C_1112,A_1113] :
      ( k3_xboole_0(B_1111,C_1112) = A_1113
      | ~ r1_tarski(k3_xboole_0(B_1111,C_1112),A_1113)
      | ~ r1_tarski(A_1113,C_1112)
      | ~ r1_tarski(A_1113,B_1111) ) ),
    inference(resolution,[status(thm)],[c_125560,c_6])).

tff(c_129084,plain,(
    ! [B_1023,A_1,B_2] :
      ( k3_xboole_0(B_1023,A_1) = k3_xboole_0(A_1,B_2)
      | ~ r1_tarski(k3_xboole_0(B_1023,A_1),B_2)
      | ~ r1_tarski(k3_xboole_0(B_1023,A_1),A_1)
      | ~ r1_tarski(B_2,B_1023) ) ),
    inference(resolution,[status(thm)],[c_125479,c_129000])).

tff(c_146740,plain,(
    ! [B_1305,A_1306,B_1307] :
      ( k3_xboole_0(B_1305,A_1306) = k3_xboole_0(A_1306,B_1307)
      | ~ r1_tarski(k3_xboole_0(B_1305,A_1306),B_1307)
      | ~ r1_tarski(B_1307,B_1305) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_129084])).

tff(c_146833,plain,(
    ! [B_2,A_1,A_1033] :
      ( k3_xboole_0(B_2,k3_xboole_0(A_1,A_1033)) = k3_xboole_0(A_1,B_2)
      | ~ r1_tarski(k3_xboole_0(A_1,A_1033),A_1)
      | ~ r1_tarski(B_2,A_1033) ) ),
    inference(resolution,[status(thm)],[c_125552,c_146740])).

tff(c_167796,plain,(
    ! [B_1433,A_1434,A_1435] :
      ( k3_xboole_0(B_1433,k3_xboole_0(A_1434,A_1435)) = k3_xboole_0(A_1434,B_1433)
      | ~ r1_tarski(B_1433,A_1435) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_146833])).

tff(c_168557,plain,(
    ! [B_1433] :
      ( k3_xboole_0(B_1433,'#skF_5') = k3_xboole_0('#skF_4',B_1433)
      | ~ r1_tarski(B_1433,'#skF_1'('#skF_3','#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131949,c_167796])).

tff(c_185918,plain,
    ( k3_xboole_0(k2_pre_topc('#skF_3','#skF_5'),'#skF_5') = k3_xboole_0('#skF_4',k2_pre_topc('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_185914,c_168557])).

tff(c_185958,plain,(
    k3_xboole_0('#skF_4',k2_pre_topc('#skF_3','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_125428,c_125430,c_125427,c_130626,c_132046,c_126507,c_2,c_185918])).

tff(c_185960,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126124,c_185958])).

%------------------------------------------------------------------------------
