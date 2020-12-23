%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1401+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:54 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   58 (  73 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  153 ( 289 expanded)
%              Number of equality atoms :   14 (  27 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_setfam_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_connsp_2,type,(
    k1_connsp_2: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v3_pre_topc(C,A)
                    & v4_pre_topc(C,A)
                    & r2_hidden(B,C)
                    & r1_tarski(C,k1_connsp_2(A,B)) )
                 => C = k1_connsp_2(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_connsp_2)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = k1_connsp_2(A,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
                    & ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(E,D)
                        <=> ( v3_pre_topc(E,A)
                            & v4_pre_topc(E,A)
                            & r2_hidden(B,E) ) ) )
                    & k6_setfam_1(u1_struct_0(A),D) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_connsp_2)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_58,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_50,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_62,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_60,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_54,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_52,plain,(
    v4_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_38,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k1_connsp_2(A_56,B_57),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_subset_1(B_57,u1_struct_0(A_56))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_136,plain,(
    ! [E_109,A_110,B_111] :
      ( r2_hidden(E_109,'#skF_1'(A_110,B_111,k1_connsp_2(A_110,B_111)))
      | ~ r2_hidden(B_111,E_109)
      | ~ v4_pre_topc(E_109,A_110)
      | ~ v3_pre_topc(E_109,A_110)
      | ~ m1_subset_1(E_109,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ m1_subset_1(k1_connsp_2(A_110,B_111),k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ m1_subset_1(B_111,u1_struct_0(A_110))
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_139,plain,(
    ! [E_109,A_56,B_57] :
      ( r2_hidden(E_109,'#skF_1'(A_56,B_57,k1_connsp_2(A_56,B_57)))
      | ~ r2_hidden(B_57,E_109)
      | ~ v4_pre_topc(E_109,A_56)
      | ~ v3_pre_topc(E_109,A_56)
      | ~ m1_subset_1(E_109,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_subset_1(B_57,u1_struct_0(A_56))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_38,c_136])).

tff(c_107,plain,(
    ! [A_89,B_90] :
      ( m1_subset_1('#skF_1'(A_89,B_90,k1_connsp_2(A_89,B_90)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_89))))
      | ~ m1_subset_1(k1_connsp_2(A_89,B_90),k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ m1_subset_1(B_90,u1_struct_0(A_89))
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40,plain,(
    ! [A_58,B_59] :
      ( k6_setfam_1(A_58,B_59) = k1_setfam_1(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k1_zfmisc_1(A_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_132,plain,(
    ! [A_107,B_108] :
      ( k6_setfam_1(u1_struct_0(A_107),'#skF_1'(A_107,B_108,k1_connsp_2(A_107,B_108))) = k1_setfam_1('#skF_1'(A_107,B_108,k1_connsp_2(A_107,B_108)))
      | ~ m1_subset_1(k1_connsp_2(A_107,B_108),k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ m1_subset_1(B_108,u1_struct_0(A_107))
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(resolution,[status(thm)],[c_107,c_40])).

tff(c_140,plain,(
    ! [A_112,B_113] :
      ( k6_setfam_1(u1_struct_0(A_112),'#skF_1'(A_112,B_113,k1_connsp_2(A_112,B_113))) = k1_setfam_1('#skF_1'(A_112,B_113,k1_connsp_2(A_112,B_113)))
      | ~ m1_subset_1(B_113,u1_struct_0(A_112))
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112)
      | v2_struct_0(A_112) ) ),
    inference(resolution,[status(thm)],[c_38,c_132])).

tff(c_115,plain,(
    ! [A_91,B_92] :
      ( k6_setfam_1(u1_struct_0(A_91),'#skF_1'(A_91,B_92,k1_connsp_2(A_91,B_92))) = k1_connsp_2(A_91,B_92)
      | ~ m1_subset_1(k1_connsp_2(A_91,B_92),k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ m1_subset_1(B_92,u1_struct_0(A_91))
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_118,plain,(
    ! [A_56,B_57] :
      ( k6_setfam_1(u1_struct_0(A_56),'#skF_1'(A_56,B_57,k1_connsp_2(A_56,B_57))) = k1_connsp_2(A_56,B_57)
      | ~ m1_subset_1(B_57,u1_struct_0(A_56))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_38,c_115])).

tff(c_155,plain,(
    ! [A_114,B_115] :
      ( k1_setfam_1('#skF_1'(A_114,B_115,k1_connsp_2(A_114,B_115))) = k1_connsp_2(A_114,B_115)
      | ~ m1_subset_1(B_115,u1_struct_0(A_114))
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114)
      | ~ m1_subset_1(B_115,u1_struct_0(A_114))
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_118])).

tff(c_42,plain,(
    ! [B_61,A_60] :
      ( r1_tarski(k1_setfam_1(B_61),A_60)
      | ~ r2_hidden(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_189,plain,(
    ! [A_119,B_120,A_121] :
      ( r1_tarski(k1_connsp_2(A_119,B_120),A_121)
      | ~ r2_hidden(A_121,'#skF_1'(A_119,B_120,k1_connsp_2(A_119,B_120)))
      | ~ m1_subset_1(B_120,u1_struct_0(A_119))
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119)
      | ~ m1_subset_1(B_120,u1_struct_0(A_119))
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_42])).

tff(c_204,plain,(
    ! [A_125,B_126,E_127] :
      ( r1_tarski(k1_connsp_2(A_125,B_126),E_127)
      | ~ r2_hidden(B_126,E_127)
      | ~ v4_pre_topc(E_127,A_125)
      | ~ v3_pre_topc(E_127,A_125)
      | ~ m1_subset_1(E_127,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ m1_subset_1(B_126,u1_struct_0(A_125))
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125)
      | v2_struct_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_139,c_189])).

tff(c_210,plain,(
    ! [B_126] :
      ( r1_tarski(k1_connsp_2('#skF_3',B_126),'#skF_5')
      | ~ r2_hidden(B_126,'#skF_5')
      | ~ v4_pre_topc('#skF_5','#skF_3')
      | ~ v3_pre_topc('#skF_5','#skF_3')
      | ~ m1_subset_1(B_126,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_204])).

tff(c_215,plain,(
    ! [B_126] :
      ( r1_tarski(k1_connsp_2('#skF_3',B_126),'#skF_5')
      | ~ r2_hidden(B_126,'#skF_5')
      | ~ m1_subset_1(B_126,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_54,c_52,c_210])).

tff(c_217,plain,(
    ! [B_128] :
      ( r1_tarski(k1_connsp_2('#skF_3',B_128),'#skF_5')
      | ~ r2_hidden(B_128,'#skF_5')
      | ~ m1_subset_1(B_128,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_215])).

tff(c_46,plain,(
    k1_connsp_2('#skF_3','#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_48,plain,(
    r1_tarski('#skF_5',k1_connsp_2('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_68,plain,(
    ! [B_72,A_73] :
      ( B_72 = A_73
      | ~ r1_tarski(B_72,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_72,plain,
    ( k1_connsp_2('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski(k1_connsp_2('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_68])).

tff(c_78,plain,(
    ~ r1_tarski(k1_connsp_2('#skF_3','#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_72])).

tff(c_220,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_217,c_78])).

tff(c_226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_220])).

%------------------------------------------------------------------------------
