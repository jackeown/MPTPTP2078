%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1401+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:54 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.87s
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

tff(f_108,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_connsp_2)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_connsp_2)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_60,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_52,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_64,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_62,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_56,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_54,plain,(
    v4_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_38,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k1_connsp_2(A_56,B_57),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_subset_1(B_57,u1_struct_0(A_56))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_226,plain,(
    ! [E_117,A_118,B_119] :
      ( r2_hidden(E_117,'#skF_1'(A_118,B_119,k1_connsp_2(A_118,B_119)))
      | ~ r2_hidden(B_119,E_117)
      | ~ v4_pre_topc(E_117,A_118)
      | ~ v3_pre_topc(E_117,A_118)
      | ~ m1_subset_1(E_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ m1_subset_1(k1_connsp_2(A_118,B_119),k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ m1_subset_1(B_119,u1_struct_0(A_118))
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_232,plain,(
    ! [E_117,A_56,B_57] :
      ( r2_hidden(E_117,'#skF_1'(A_56,B_57,k1_connsp_2(A_56,B_57)))
      | ~ r2_hidden(B_57,E_117)
      | ~ v4_pre_topc(E_117,A_56)
      | ~ v3_pre_topc(E_117,A_56)
      | ~ m1_subset_1(E_117,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_subset_1(B_57,u1_struct_0(A_56))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_38,c_226])).

tff(c_149,plain,(
    ! [A_94,B_95] :
      ( m1_subset_1('#skF_1'(A_94,B_95,k1_connsp_2(A_94,B_95)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_94))))
      | ~ m1_subset_1(k1_connsp_2(A_94,B_95),k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ m1_subset_1(B_95,u1_struct_0(A_94))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40,plain,(
    ! [A_58,B_59] :
      ( k6_setfam_1(A_58,B_59) = k1_setfam_1(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k1_zfmisc_1(A_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_186,plain,(
    ! [A_111,B_112] :
      ( k6_setfam_1(u1_struct_0(A_111),'#skF_1'(A_111,B_112,k1_connsp_2(A_111,B_112))) = k1_setfam_1('#skF_1'(A_111,B_112,k1_connsp_2(A_111,B_112)))
      | ~ m1_subset_1(k1_connsp_2(A_111,B_112),k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ m1_subset_1(B_112,u1_struct_0(A_111))
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(resolution,[status(thm)],[c_149,c_40])).

tff(c_194,plain,(
    ! [A_113,B_114] :
      ( k6_setfam_1(u1_struct_0(A_113),'#skF_1'(A_113,B_114,k1_connsp_2(A_113,B_114))) = k1_setfam_1('#skF_1'(A_113,B_114,k1_connsp_2(A_113,B_114)))
      | ~ m1_subset_1(B_114,u1_struct_0(A_113))
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_38,c_186])).

tff(c_158,plain,(
    ! [A_96,B_97] :
      ( k6_setfam_1(u1_struct_0(A_96),'#skF_1'(A_96,B_97,k1_connsp_2(A_96,B_97))) = k1_connsp_2(A_96,B_97)
      | ~ m1_subset_1(k1_connsp_2(A_96,B_97),k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m1_subset_1(B_97,u1_struct_0(A_96))
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_164,plain,(
    ! [A_56,B_57] :
      ( k6_setfam_1(u1_struct_0(A_56),'#skF_1'(A_56,B_57,k1_connsp_2(A_56,B_57))) = k1_connsp_2(A_56,B_57)
      | ~ m1_subset_1(B_57,u1_struct_0(A_56))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_38,c_158])).

tff(c_209,plain,(
    ! [A_115,B_116] :
      ( k1_setfam_1('#skF_1'(A_115,B_116,k1_connsp_2(A_115,B_116))) = k1_connsp_2(A_115,B_116)
      | ~ m1_subset_1(B_116,u1_struct_0(A_115))
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115)
      | ~ m1_subset_1(B_116,u1_struct_0(A_115))
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_164])).

tff(c_46,plain,(
    ! [B_63,A_62] :
      ( r1_tarski(k1_setfam_1(B_63),A_62)
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_253,plain,(
    ! [A_123,B_124,A_125] :
      ( r1_tarski(k1_connsp_2(A_123,B_124),A_125)
      | ~ r2_hidden(A_125,'#skF_1'(A_123,B_124,k1_connsp_2(A_123,B_124)))
      | ~ m1_subset_1(B_124,u1_struct_0(A_123))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123)
      | ~ m1_subset_1(B_124,u1_struct_0(A_123))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_46])).

tff(c_274,plain,(
    ! [A_129,B_130,E_131] :
      ( r1_tarski(k1_connsp_2(A_129,B_130),E_131)
      | ~ r2_hidden(B_130,E_131)
      | ~ v4_pre_topc(E_131,A_129)
      | ~ v3_pre_topc(E_131,A_129)
      | ~ m1_subset_1(E_131,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ m1_subset_1(B_130,u1_struct_0(A_129))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(resolution,[status(thm)],[c_232,c_253])).

tff(c_283,plain,(
    ! [B_130] :
      ( r1_tarski(k1_connsp_2('#skF_3',B_130),'#skF_5')
      | ~ r2_hidden(B_130,'#skF_5')
      | ~ v4_pre_topc('#skF_5','#skF_3')
      | ~ v3_pre_topc('#skF_5','#skF_3')
      | ~ m1_subset_1(B_130,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_58,c_274])).

tff(c_289,plain,(
    ! [B_130] :
      ( r1_tarski(k1_connsp_2('#skF_3',B_130),'#skF_5')
      | ~ r2_hidden(B_130,'#skF_5')
      | ~ m1_subset_1(B_130,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_56,c_54,c_283])).

tff(c_291,plain,(
    ! [B_132] :
      ( r1_tarski(k1_connsp_2('#skF_3',B_132),'#skF_5')
      | ~ r2_hidden(B_132,'#skF_5')
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_289])).

tff(c_48,plain,(
    k1_connsp_2('#skF_3','#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_50,plain,(
    r1_tarski('#skF_5',k1_connsp_2('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_80,plain,(
    ! [B_75,A_76] :
      ( B_75 = A_76
      | ~ r1_tarski(B_75,A_76)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_86,plain,
    ( k1_connsp_2('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski(k1_connsp_2('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_80])).

tff(c_93,plain,(
    ~ r1_tarski(k1_connsp_2('#skF_3','#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_86])).

tff(c_294,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_291,c_93])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_52,c_294])).

%------------------------------------------------------------------------------
