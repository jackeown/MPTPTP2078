%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1109+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:25 EST 2020

% Result     : Theorem 8.74s
% Output     : CNFRefutation 8.74s
% Verified   : 
% Statistics : Number of formulae       :  175 (13716 expanded)
%              Number of leaves         :   28 (4663 expanded)
%              Depth                    :   31
%              Number of atoms          :  580 (37845 expanded)
%              Number of equality atoms :  106 (12019 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( l1_pre_topc(C)
               => ! [D] :
                    ( l1_pre_topc(D)
                   => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                        & g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D),u1_pre_topc(D))
                        & m1_pre_topc(C,A) )
                     => m1_pre_topc(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(B,A)
          <=> ( r1_tarski(k2_struct_0(B),k2_struct_0(A))
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
                 => ( r2_hidden(C,u1_pre_topc(B))
                  <=> ? [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(D,u1_pre_topc(A))
                        & C = k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_28,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_42,plain,(
    ~ m1_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_54,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_56,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_52,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_44,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_22,plain,(
    ! [B_24,A_2] :
      ( r1_tarski(k2_struct_0(B_24),k2_struct_0(A_2))
      | ~ m1_pre_topc(B_24,A_2)
      | ~ l1_pre_topc(B_24)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_32,plain,(
    ! [A_42] :
      ( l1_struct_0(A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_58,plain,(
    ! [A_65] :
      ( u1_struct_0(A_65) = k2_struct_0(A_65)
      | ~ l1_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_63,plain,(
    ! [A_66] :
      ( u1_struct_0(A_66) = k2_struct_0(A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_32,c_58])).

tff(c_78,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_63])).

tff(c_108,plain,(
    ! [A_69] :
      ( m1_subset_1(u1_pre_topc(A_69),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_69))))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_114,plain,
    ( m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5'))))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_108])).

tff(c_124,plain,(
    m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_114])).

tff(c_79,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_63])).

tff(c_48,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_129,plain,(
    g1_pre_topc(k2_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_79,c_48])).

tff(c_144,plain,(
    ! [C_72,A_73,D_74,B_75] :
      ( C_72 = A_73
      | g1_pre_topc(C_72,D_74) != g1_pre_topc(A_73,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k1_zfmisc_1(A_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_152,plain,(
    ! [C_72,D_74] :
      ( k2_struct_0('#skF_5') = C_72
      | g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_72,D_74)
      | ~ m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_144])).

tff(c_156,plain,(
    ! [C_72,D_74] :
      ( k2_struct_0('#skF_5') = C_72
      | g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_72,D_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_152])).

tff(c_268,plain,(
    k2_struct_0('#skF_5') = k2_struct_0('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_156])).

tff(c_117,plain,
    ( m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_108])).

tff(c_126,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_117])).

tff(c_173,plain,(
    ! [D_78,B_79,C_80,A_81] :
      ( D_78 = B_79
      | g1_pre_topc(C_80,D_78) != g1_pre_topc(A_81,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k1_zfmisc_1(A_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_350,plain,(
    ! [B_92,A_93] :
      ( u1_pre_topc('#skF_5') = B_92
      | g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(A_93,B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k1_zfmisc_1(A_93))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_173])).

tff(c_373,plain,(
    u1_pre_topc('#skF_5') = u1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_126,c_350])).

tff(c_281,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_78])).

tff(c_76,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_63])).

tff(c_779,plain,(
    ! [B_156,D_157,A_158] :
      ( k9_subset_1(u1_struct_0(B_156),D_157,k2_struct_0(B_156)) != '#skF_2'(A_158,B_156)
      | ~ r2_hidden(D_157,u1_pre_topc(A_158))
      | ~ m1_subset_1(D_157,k1_zfmisc_1(u1_struct_0(A_158)))
      | r2_hidden('#skF_3'(A_158,B_156),u1_pre_topc(A_158))
      | m1_pre_topc(B_156,A_158)
      | ~ r1_tarski(k2_struct_0(B_156),k2_struct_0(A_158))
      | ~ l1_pre_topc(B_156)
      | ~ l1_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_795,plain,(
    ! [D_157,A_158] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_157,k2_struct_0('#skF_6')) != '#skF_2'(A_158,'#skF_6')
      | ~ r2_hidden(D_157,u1_pre_topc(A_158))
      | ~ m1_subset_1(D_157,k1_zfmisc_1(u1_struct_0(A_158)))
      | r2_hidden('#skF_3'(A_158,'#skF_6'),u1_pre_topc(A_158))
      | m1_pre_topc('#skF_6',A_158)
      | ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0(A_158))
      | ~ l1_pre_topc('#skF_6')
      | ~ l1_pre_topc(A_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_779])).

tff(c_942,plain,(
    ! [D_168,A_169] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_168,k2_struct_0('#skF_6')) != '#skF_2'(A_169,'#skF_6')
      | ~ r2_hidden(D_168,u1_pre_topc(A_169))
      | ~ m1_subset_1(D_168,k1_zfmisc_1(u1_struct_0(A_169)))
      | r2_hidden('#skF_3'(A_169,'#skF_6'),u1_pre_topc(A_169))
      | m1_pre_topc('#skF_6',A_169)
      | ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0(A_169))
      | ~ l1_pre_topc(A_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_795])).

tff(c_948,plain,(
    ! [D_168] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_168,k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_6')
      | ~ r2_hidden(D_168,u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(D_168,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | r2_hidden('#skF_3'('#skF_5','#skF_6'),u1_pre_topc('#skF_5'))
      | m1_pre_topc('#skF_6','#skF_5')
      | ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_942])).

tff(c_960,plain,(
    ! [D_168] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_168,k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_6')
      | ~ r2_hidden(D_168,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(D_168,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | r2_hidden('#skF_3'('#skF_5','#skF_6'),u1_pre_topc('#skF_4'))
      | m1_pre_topc('#skF_6','#skF_5')
      | ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_268,c_373,c_373,c_948])).

tff(c_1159,plain,(
    ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_960])).

tff(c_1168,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_1159])).

tff(c_1178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_44,c_1168])).

tff(c_1180,plain,(
    r1_tarski(k2_struct_0('#skF_6'),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_960])).

tff(c_50,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_77,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_63])).

tff(c_111,plain,
    ( m1_subset_1(u1_pre_topc('#skF_7'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_7'))))
    | ~ l1_pre_topc('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_108])).

tff(c_122,plain,(
    m1_subset_1(u1_pre_topc('#skF_7'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_7')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_111])).

tff(c_46,plain,(
    g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7')) = g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_84,plain,(
    g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7')) = g1_pre_topc(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_46])).

tff(c_134,plain,(
    g1_pre_topc(k2_struct_0('#skF_7'),u1_pre_topc('#skF_7')) = g1_pre_topc(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_84])).

tff(c_148,plain,(
    ! [C_72,D_74] :
      ( k2_struct_0('#skF_7') = C_72
      | g1_pre_topc(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6')) != g1_pre_topc(C_72,D_74)
      | ~ m1_subset_1(u1_pre_topc('#skF_7'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_7')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_144])).

tff(c_154,plain,(
    ! [C_72,D_74] :
      ( k2_struct_0('#skF_7') = C_72
      | g1_pre_topc(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6')) != g1_pre_topc(C_72,D_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_148])).

tff(c_159,plain,(
    k2_struct_0('#skF_7') = k2_struct_0('#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_154])).

tff(c_189,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_77])).

tff(c_239,plain,(
    ! [A_83,B_84] :
      ( m1_subset_1('#skF_2'(A_83,B_84),k1_zfmisc_1(u1_struct_0(B_84)))
      | m1_pre_topc(B_84,A_83)
      | ~ r1_tarski(k2_struct_0(B_84),k2_struct_0(A_83))
      | ~ l1_pre_topc(B_84)
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_242,plain,(
    ! [A_83] :
      ( m1_subset_1('#skF_2'(A_83,'#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_6')))
      | m1_pre_topc('#skF_7',A_83)
      | ~ r1_tarski(k2_struct_0('#skF_7'),k2_struct_0(A_83))
      | ~ l1_pre_topc('#skF_7')
      | ~ l1_pre_topc(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_239])).

tff(c_253,plain,(
    ! [A_83] :
      ( m1_subset_1('#skF_2'(A_83,'#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_6')))
      | m1_pre_topc('#skF_7',A_83)
      | ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0(A_83))
      | ~ l1_pre_topc(A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_159,c_242])).

tff(c_177,plain,(
    ! [D_78,C_80] :
      ( u1_pre_topc('#skF_7') = D_78
      | g1_pre_topc(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6')) != g1_pre_topc(C_80,D_78)
      | ~ m1_subset_1(u1_pre_topc('#skF_7'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_7')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_173])).

tff(c_183,plain,(
    ! [D_78,C_80] :
      ( u1_pre_topc('#skF_7') = D_78
      | g1_pre_topc(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6')) != g1_pre_topc(C_80,D_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_177])).

tff(c_407,plain,(
    u1_pre_topc('#skF_7') = u1_pre_topc('#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_183])).

tff(c_824,plain,(
    ! [B_160,D_161,A_162] :
      ( k9_subset_1(u1_struct_0(B_160),D_161,k2_struct_0(B_160)) != '#skF_2'(A_162,B_160)
      | ~ r2_hidden(D_161,u1_pre_topc(A_162))
      | ~ m1_subset_1(D_161,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ r2_hidden('#skF_2'(A_162,B_160),u1_pre_topc(B_160))
      | m1_pre_topc(B_160,A_162)
      | ~ r1_tarski(k2_struct_0(B_160),k2_struct_0(A_162))
      | ~ l1_pre_topc(B_160)
      | ~ l1_pre_topc(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_834,plain,(
    ! [D_161,A_162] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_161,k2_struct_0('#skF_7')) != '#skF_2'(A_162,'#skF_7')
      | ~ r2_hidden(D_161,u1_pre_topc(A_162))
      | ~ m1_subset_1(D_161,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ r2_hidden('#skF_2'(A_162,'#skF_7'),u1_pre_topc('#skF_7'))
      | m1_pre_topc('#skF_7',A_162)
      | ~ r1_tarski(k2_struct_0('#skF_7'),k2_struct_0(A_162))
      | ~ l1_pre_topc('#skF_7')
      | ~ l1_pre_topc(A_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_824])).

tff(c_5249,plain,(
    ! [D_614,A_615] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_614,k2_struct_0('#skF_6')) != '#skF_2'(A_615,'#skF_7')
      | ~ r2_hidden(D_614,u1_pre_topc(A_615))
      | ~ m1_subset_1(D_614,k1_zfmisc_1(u1_struct_0(A_615)))
      | ~ r2_hidden('#skF_2'(A_615,'#skF_7'),u1_pre_topc('#skF_6'))
      | m1_pre_topc('#skF_7',A_615)
      | ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0(A_615))
      | ~ l1_pre_topc(A_615) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_159,c_407,c_159,c_834])).

tff(c_5255,plain,(
    ! [D_614] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_614,k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden(D_614,u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(D_614,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ r2_hidden('#skF_2'('#skF_5','#skF_7'),u1_pre_topc('#skF_6'))
      | m1_pre_topc('#skF_7','#skF_5')
      | ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_5249])).

tff(c_5267,plain,(
    ! [D_614] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_614,k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden(D_614,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(D_614,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ r2_hidden('#skF_2'('#skF_5','#skF_7'),u1_pre_topc('#skF_6'))
      | m1_pre_topc('#skF_7','#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1180,c_268,c_373,c_5255])).

tff(c_5268,plain,(
    ! [D_614] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_614,k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden(D_614,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(D_614,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ r2_hidden('#skF_2'('#skF_5','#skF_7'),u1_pre_topc('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_5267])).

tff(c_5278,plain,(
    ~ r2_hidden('#skF_2'('#skF_5','#skF_7'),u1_pre_topc('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_5268])).

tff(c_414,plain,(
    ! [A_97,B_98] :
      ( r2_hidden('#skF_2'(A_97,B_98),u1_pre_topc(B_98))
      | r2_hidden('#skF_3'(A_97,B_98),u1_pre_topc(A_97))
      | m1_pre_topc(B_98,A_97)
      | ~ r1_tarski(k2_struct_0(B_98),k2_struct_0(A_97))
      | ~ l1_pre_topc(B_98)
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_418,plain,(
    ! [B_98] :
      ( r2_hidden('#skF_2'('#skF_5',B_98),u1_pre_topc(B_98))
      | r2_hidden('#skF_3'('#skF_5',B_98),u1_pre_topc('#skF_4'))
      | m1_pre_topc(B_98,'#skF_5')
      | ~ r1_tarski(k2_struct_0(B_98),k2_struct_0('#skF_5'))
      | ~ l1_pre_topc(B_98)
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_414])).

tff(c_420,plain,(
    ! [B_98] :
      ( r2_hidden('#skF_2'('#skF_5',B_98),u1_pre_topc(B_98))
      | r2_hidden('#skF_3'('#skF_5',B_98),u1_pre_topc('#skF_4'))
      | m1_pre_topc(B_98,'#skF_5')
      | ~ r1_tarski(k2_struct_0(B_98),k2_struct_0('#skF_4'))
      | ~ l1_pre_topc(B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_268,c_418])).

tff(c_621,plain,(
    ! [A_145,B_146] :
      ( r2_hidden('#skF_2'(A_145,B_146),u1_pre_topc(B_146))
      | k9_subset_1(u1_struct_0(B_146),'#skF_3'(A_145,B_146),k2_struct_0(B_146)) = '#skF_2'(A_145,B_146)
      | m1_pre_topc(B_146,A_145)
      | ~ r1_tarski(k2_struct_0(B_146),k2_struct_0(A_145))
      | ~ l1_pre_topc(B_146)
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_636,plain,(
    ! [A_145] :
      ( r2_hidden('#skF_2'(A_145,'#skF_7'),u1_pre_topc('#skF_7'))
      | k9_subset_1(k2_struct_0('#skF_6'),'#skF_3'(A_145,'#skF_7'),k2_struct_0('#skF_7')) = '#skF_2'(A_145,'#skF_7')
      | m1_pre_topc('#skF_7',A_145)
      | ~ r1_tarski(k2_struct_0('#skF_7'),k2_struct_0(A_145))
      | ~ l1_pre_topc('#skF_7')
      | ~ l1_pre_topc(A_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_621])).

tff(c_653,plain,(
    ! [A_145] :
      ( r2_hidden('#skF_2'(A_145,'#skF_7'),u1_pre_topc('#skF_6'))
      | k9_subset_1(k2_struct_0('#skF_6'),'#skF_3'(A_145,'#skF_7'),k2_struct_0('#skF_6')) = '#skF_2'(A_145,'#skF_7')
      | m1_pre_topc('#skF_7',A_145)
      | ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0(A_145))
      | ~ l1_pre_topc(A_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_159,c_159,c_407,c_636])).

tff(c_499,plain,(
    ! [A_114,B_115] :
      ( r2_hidden('#skF_2'(A_114,B_115),u1_pre_topc(B_115))
      | m1_subset_1('#skF_3'(A_114,B_115),k1_zfmisc_1(u1_struct_0(A_114)))
      | m1_pre_topc(B_115,A_114)
      | ~ r1_tarski(k2_struct_0(B_115),k2_struct_0(A_114))
      | ~ l1_pre_topc(B_115)
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_504,plain,(
    ! [B_115] :
      ( r2_hidden('#skF_2'('#skF_5',B_115),u1_pre_topc(B_115))
      | m1_subset_1('#skF_3'('#skF_5',B_115),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | m1_pre_topc(B_115,'#skF_5')
      | ~ r1_tarski(k2_struct_0(B_115),k2_struct_0('#skF_5'))
      | ~ l1_pre_topc(B_115)
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_499])).

tff(c_515,plain,(
    ! [B_115] :
      ( r2_hidden('#skF_2'('#skF_5',B_115),u1_pre_topc(B_115))
      | m1_subset_1('#skF_3'('#skF_5',B_115),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | m1_pre_topc(B_115,'#skF_5')
      | ~ r1_tarski(k2_struct_0(B_115),k2_struct_0('#skF_4'))
      | ~ l1_pre_topc(B_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_268,c_504])).

tff(c_1179,plain,(
    ! [D_168] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_168,k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_6')
      | ~ r2_hidden(D_168,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(D_168,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | m1_pre_topc('#skF_6','#skF_5')
      | r2_hidden('#skF_3'('#skF_5','#skF_6'),u1_pre_topc('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_960])).

tff(c_1194,plain,(
    ! [D_183] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_183,k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_6')
      | ~ r2_hidden(D_183,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(D_183,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(splitLeft,[status(thm)],[c_1179])).

tff(c_1365,plain,(
    ! [B_192] :
      ( k9_subset_1(k2_struct_0('#skF_6'),'#skF_3'('#skF_5',B_192),k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_6')
      | ~ r2_hidden('#skF_3'('#skF_5',B_192),u1_pre_topc('#skF_4'))
      | r2_hidden('#skF_2'('#skF_5',B_192),u1_pre_topc(B_192))
      | m1_pre_topc(B_192,'#skF_5')
      | ~ r1_tarski(k2_struct_0(B_192),k2_struct_0('#skF_4'))
      | ~ l1_pre_topc(B_192) ) ),
    inference(resolution,[status(thm)],[c_515,c_1194])).

tff(c_1368,plain,
    ( '#skF_2'('#skF_5','#skF_7') != '#skF_2'('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_7'),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_2'('#skF_5','#skF_7'),u1_pre_topc('#skF_7'))
    | m1_pre_topc('#skF_7','#skF_5')
    | ~ r1_tarski(k2_struct_0('#skF_7'),k2_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_7')
    | r2_hidden('#skF_2'('#skF_5','#skF_7'),u1_pre_topc('#skF_6'))
    | m1_pre_topc('#skF_7','#skF_5')
    | ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_1365])).

tff(c_1373,plain,
    ( '#skF_2'('#skF_5','#skF_7') != '#skF_2'('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_7'),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_2'('#skF_5','#skF_7'),u1_pre_topc('#skF_6'))
    | m1_pre_topc('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1180,c_268,c_50,c_1180,c_159,c_407,c_1368])).

tff(c_1374,plain,
    ( '#skF_2'('#skF_5','#skF_7') != '#skF_2'('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_7'),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_2'('#skF_5','#skF_7'),u1_pre_topc('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1373])).

tff(c_3769,plain,(
    ~ r2_hidden('#skF_3'('#skF_5','#skF_7'),u1_pre_topc('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1374])).

tff(c_3772,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_7'),u1_pre_topc('#skF_7'))
    | m1_pre_topc('#skF_7','#skF_5')
    | ~ r1_tarski(k2_struct_0('#skF_7'),k2_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_420,c_3769])).

tff(c_3775,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_7'),u1_pre_topc('#skF_6'))
    | m1_pre_topc('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1180,c_159,c_407,c_3772])).

tff(c_3776,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_7'),u1_pre_topc('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_3775])).

tff(c_28,plain,(
    ! [A_2,B_24,C_35] :
      ( r2_hidden('#skF_1'(A_2,B_24,C_35),u1_pre_topc(A_2))
      | ~ r2_hidden(C_35,u1_pre_topc(B_24))
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0(B_24)))
      | ~ m1_pre_topc(B_24,A_2)
      | ~ l1_pre_topc(B_24)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_534,plain,(
    ! [B_130,A_131,C_132] :
      ( k9_subset_1(u1_struct_0(B_130),'#skF_1'(A_131,B_130,C_132),k2_struct_0(B_130)) = C_132
      | ~ r2_hidden(C_132,u1_pre_topc(B_130))
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0(B_130)))
      | ~ m1_pre_topc(B_130,A_131)
      | ~ l1_pre_topc(B_130)
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_558,plain,(
    ! [A_131,C_132] :
      ( k9_subset_1(k2_struct_0('#skF_6'),'#skF_1'(A_131,'#skF_6',C_132),k2_struct_0('#skF_6')) = C_132
      | ~ r2_hidden(C_132,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc('#skF_6',A_131)
      | ~ l1_pre_topc('#skF_6')
      | ~ l1_pre_topc(A_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_534])).

tff(c_572,plain,(
    ! [A_131,C_132] :
      ( k9_subset_1(k2_struct_0('#skF_6'),'#skF_1'(A_131,'#skF_6',C_132),k2_struct_0('#skF_6')) = C_132
      | ~ r2_hidden(C_132,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_struct_0('#skF_6')))
      | ~ m1_pre_topc('#skF_6',A_131)
      | ~ l1_pre_topc(A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_76,c_558])).

tff(c_469,plain,(
    ! [A_107,B_108,C_109] :
      ( m1_subset_1('#skF_1'(A_107,B_108,C_109),k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ r2_hidden(C_109,u1_pre_topc(B_108))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(u1_struct_0(B_108)))
      | ~ m1_pre_topc(B_108,A_107)
      | ~ l1_pre_topc(B_108)
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_478,plain,(
    ! [B_108,C_109] :
      ( m1_subset_1('#skF_1'('#skF_4',B_108,C_109),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ r2_hidden(C_109,u1_pre_topc(B_108))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(u1_struct_0(B_108)))
      | ~ m1_pre_topc(B_108,'#skF_4')
      | ~ l1_pre_topc(B_108)
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_469])).

tff(c_487,plain,(
    ! [B_108,C_109] :
      ( m1_subset_1('#skF_1'('#skF_4',B_108,C_109),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ r2_hidden(C_109,u1_pre_topc(B_108))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(u1_struct_0(B_108)))
      | ~ m1_pre_topc(B_108,'#skF_4')
      | ~ l1_pre_topc(B_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_478])).

tff(c_4426,plain,(
    ! [D_523,A_524] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_523,k2_struct_0('#skF_6')) != '#skF_2'(A_524,'#skF_7')
      | ~ r2_hidden(D_523,u1_pre_topc(A_524))
      | ~ m1_subset_1(D_523,k1_zfmisc_1(u1_struct_0(A_524)))
      | ~ r2_hidden('#skF_2'(A_524,'#skF_7'),u1_pre_topc('#skF_6'))
      | m1_pre_topc('#skF_7',A_524)
      | ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0(A_524))
      | ~ l1_pre_topc(A_524) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_159,c_407,c_159,c_834])).

tff(c_4432,plain,(
    ! [D_523] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_523,k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden(D_523,u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(D_523,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ r2_hidden('#skF_2'('#skF_5','#skF_7'),u1_pre_topc('#skF_6'))
      | m1_pre_topc('#skF_7','#skF_5')
      | ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_4426])).

tff(c_4444,plain,(
    ! [D_523] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_523,k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden(D_523,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(D_523,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | m1_pre_topc('#skF_7','#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1180,c_268,c_3776,c_373,c_4432])).

tff(c_4455,plain,(
    ! [D_525] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_525,k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden(D_525,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(D_525,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_4444])).

tff(c_4515,plain,(
    ! [B_533,C_534] :
      ( k9_subset_1(k2_struct_0('#skF_6'),'#skF_1'('#skF_4',B_533,C_534),k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_4',B_533,C_534),u1_pre_topc('#skF_4'))
      | ~ r2_hidden(C_534,u1_pre_topc(B_533))
      | ~ m1_subset_1(C_534,k1_zfmisc_1(u1_struct_0(B_533)))
      | ~ m1_pre_topc(B_533,'#skF_4')
      | ~ l1_pre_topc(B_533) ) ),
    inference(resolution,[status(thm)],[c_487,c_4455])).

tff(c_4523,plain,(
    ! [C_132] :
      ( C_132 != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_4','#skF_6',C_132),u1_pre_topc('#skF_4'))
      | ~ r2_hidden(C_132,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | ~ l1_pre_topc('#skF_6')
      | ~ r2_hidden(C_132,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_struct_0('#skF_6')))
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_4515])).

tff(c_4529,plain,(
    ! [C_535] :
      ( C_535 != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_4','#skF_6',C_535),u1_pre_topc('#skF_4'))
      | ~ r2_hidden(C_535,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(C_535,k1_zfmisc_1(k2_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_44,c_52,c_44,c_76,c_4523])).

tff(c_4533,plain,(
    ! [C_35] :
      ( C_35 != '#skF_2'('#skF_5','#skF_7')
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_struct_0('#skF_6')))
      | ~ r2_hidden(C_35,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | ~ l1_pre_topc('#skF_6')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_4529])).

tff(c_4538,plain,(
    ! [C_536] :
      ( C_536 != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden(C_536,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(C_536,k1_zfmisc_1(k2_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_44,c_76,c_4533])).

tff(c_4563,plain,(
    ! [A_537] :
      ( '#skF_2'(A_537,'#skF_7') != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden('#skF_2'(A_537,'#skF_7'),u1_pre_topc('#skF_6'))
      | m1_pre_topc('#skF_7',A_537)
      | ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0(A_537))
      | ~ l1_pre_topc(A_537) ) ),
    inference(resolution,[status(thm)],[c_253,c_4538])).

tff(c_4566,plain,
    ( m1_pre_topc('#skF_7','#skF_5')
    | ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_3776,c_4563])).

tff(c_4569,plain,(
    m1_pre_topc('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1180,c_268,c_4566])).

tff(c_4571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_4569])).

tff(c_4573,plain,(
    r2_hidden('#skF_3'('#skF_5','#skF_7'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1374])).

tff(c_912,plain,(
    ! [B_165,D_166,A_167] :
      ( k9_subset_1(u1_struct_0(B_165),D_166,k2_struct_0(B_165)) != '#skF_2'(A_167,B_165)
      | ~ r2_hidden(D_166,u1_pre_topc(A_167))
      | ~ m1_subset_1(D_166,k1_zfmisc_1(u1_struct_0(A_167)))
      | m1_subset_1('#skF_3'(A_167,B_165),k1_zfmisc_1(u1_struct_0(A_167)))
      | m1_pre_topc(B_165,A_167)
      | ~ r1_tarski(k2_struct_0(B_165),k2_struct_0(A_167))
      | ~ l1_pre_topc(B_165)
      | ~ l1_pre_topc(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_922,plain,(
    ! [D_166,A_167] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_166,k2_struct_0('#skF_7')) != '#skF_2'(A_167,'#skF_7')
      | ~ r2_hidden(D_166,u1_pre_topc(A_167))
      | ~ m1_subset_1(D_166,k1_zfmisc_1(u1_struct_0(A_167)))
      | m1_subset_1('#skF_3'(A_167,'#skF_7'),k1_zfmisc_1(u1_struct_0(A_167)))
      | m1_pre_topc('#skF_7',A_167)
      | ~ r1_tarski(k2_struct_0('#skF_7'),k2_struct_0(A_167))
      | ~ l1_pre_topc('#skF_7')
      | ~ l1_pre_topc(A_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_912])).

tff(c_5403,plain,(
    ! [D_629,A_630] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_629,k2_struct_0('#skF_6')) != '#skF_2'(A_630,'#skF_7')
      | ~ r2_hidden(D_629,u1_pre_topc(A_630))
      | ~ m1_subset_1(D_629,k1_zfmisc_1(u1_struct_0(A_630)))
      | m1_subset_1('#skF_3'(A_630,'#skF_7'),k1_zfmisc_1(u1_struct_0(A_630)))
      | m1_pre_topc('#skF_7',A_630)
      | ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0(A_630))
      | ~ l1_pre_topc(A_630) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_159,c_159,c_922])).

tff(c_5409,plain,(
    ! [D_629] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_629,k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden(D_629,u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(D_629,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | m1_subset_1('#skF_3'('#skF_5','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | m1_pre_topc('#skF_7','#skF_5')
      | ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_5403])).

tff(c_5421,plain,(
    ! [D_629] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_629,k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden(D_629,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(D_629,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | m1_subset_1('#skF_3'('#skF_5','#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | m1_pre_topc('#skF_7','#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1180,c_268,c_281,c_373,c_5409])).

tff(c_5422,plain,(
    ! [D_629] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_629,k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden(D_629,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(D_629,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | m1_subset_1('#skF_3'('#skF_5','#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_5421])).

tff(c_5433,plain,(
    ! [D_631] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_631,k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden(D_631,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(D_631,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(splitLeft,[status(thm)],[c_5422])).

tff(c_5860,plain,(
    ! [B_666] :
      ( k9_subset_1(k2_struct_0('#skF_6'),'#skF_3'('#skF_5',B_666),k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden('#skF_3'('#skF_5',B_666),u1_pre_topc('#skF_4'))
      | r2_hidden('#skF_2'('#skF_5',B_666),u1_pre_topc(B_666))
      | m1_pre_topc(B_666,'#skF_5')
      | ~ r1_tarski(k2_struct_0(B_666),k2_struct_0('#skF_4'))
      | ~ l1_pre_topc(B_666) ) ),
    inference(resolution,[status(thm)],[c_515,c_5433])).

tff(c_5863,plain,
    ( ~ r2_hidden('#skF_3'('#skF_5','#skF_7'),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_2'('#skF_5','#skF_7'),u1_pre_topc('#skF_7'))
    | ~ r1_tarski(k2_struct_0('#skF_7'),k2_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_7')
    | r2_hidden('#skF_2'('#skF_5','#skF_7'),u1_pre_topc('#skF_6'))
    | m1_pre_topc('#skF_7','#skF_5')
    | ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_5860])).

tff(c_5869,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_7'),u1_pre_topc('#skF_6'))
    | m1_pre_topc('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1180,c_268,c_50,c_1180,c_159,c_407,c_4573,c_5863])).

tff(c_5871,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_5278,c_5869])).

tff(c_5872,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_5422])).

tff(c_988,plain,(
    ! [B_170,D_171,A_172] :
      ( k9_subset_1(u1_struct_0(B_170),D_171,k2_struct_0(B_170)) != '#skF_2'(A_172,B_170)
      | ~ r2_hidden(D_171,u1_pre_topc(A_172))
      | ~ m1_subset_1(D_171,k1_zfmisc_1(u1_struct_0(A_172)))
      | k9_subset_1(u1_struct_0(B_170),'#skF_3'(A_172,B_170),k2_struct_0(B_170)) = '#skF_2'(A_172,B_170)
      | m1_pre_topc(B_170,A_172)
      | ~ r1_tarski(k2_struct_0(B_170),k2_struct_0(A_172))
      | ~ l1_pre_topc(B_170)
      | ~ l1_pre_topc(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_998,plain,(
    ! [D_171,A_172] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_171,k2_struct_0('#skF_7')) != '#skF_2'(A_172,'#skF_7')
      | ~ r2_hidden(D_171,u1_pre_topc(A_172))
      | ~ m1_subset_1(D_171,k1_zfmisc_1(u1_struct_0(A_172)))
      | k9_subset_1(u1_struct_0('#skF_7'),'#skF_3'(A_172,'#skF_7'),k2_struct_0('#skF_7')) = '#skF_2'(A_172,'#skF_7')
      | m1_pre_topc('#skF_7',A_172)
      | ~ r1_tarski(k2_struct_0('#skF_7'),k2_struct_0(A_172))
      | ~ l1_pre_topc('#skF_7')
      | ~ l1_pre_topc(A_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_988])).

tff(c_6061,plain,(
    ! [D_699,A_700] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_699,k2_struct_0('#skF_6')) != '#skF_2'(A_700,'#skF_7')
      | ~ r2_hidden(D_699,u1_pre_topc(A_700))
      | ~ m1_subset_1(D_699,k1_zfmisc_1(u1_struct_0(A_700)))
      | k9_subset_1(k2_struct_0('#skF_6'),'#skF_3'(A_700,'#skF_7'),k2_struct_0('#skF_6')) = '#skF_2'(A_700,'#skF_7')
      | m1_pre_topc('#skF_7',A_700)
      | ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0(A_700))
      | ~ l1_pre_topc(A_700) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_159,c_189,c_159,c_159,c_998])).

tff(c_6067,plain,(
    ! [D_699] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_699,k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden(D_699,u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(D_699,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | k9_subset_1(k2_struct_0('#skF_6'),'#skF_3'('#skF_5','#skF_7'),k2_struct_0('#skF_6')) = '#skF_2'('#skF_5','#skF_7')
      | m1_pre_topc('#skF_7','#skF_5')
      | ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_6061])).

tff(c_6079,plain,(
    ! [D_699] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_699,k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden(D_699,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(D_699,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | k9_subset_1(k2_struct_0('#skF_6'),'#skF_3'('#skF_5','#skF_7'),k2_struct_0('#skF_6')) = '#skF_2'('#skF_5','#skF_7')
      | m1_pre_topc('#skF_7','#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1180,c_268,c_373,c_6067])).

tff(c_6080,plain,(
    ! [D_699] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_699,k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden(D_699,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(D_699,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | k9_subset_1(k2_struct_0('#skF_6'),'#skF_3'('#skF_5','#skF_7'),k2_struct_0('#skF_6')) = '#skF_2'('#skF_5','#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_6079])).

tff(c_6091,plain,(
    ! [D_701] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_701,k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden(D_701,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(D_701,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(splitLeft,[status(thm)],[c_6080])).

tff(c_6094,plain,
    ( k9_subset_1(k2_struct_0('#skF_6'),'#skF_3'('#skF_5','#skF_7'),k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_7'),u1_pre_topc('#skF_4')) ),
    inference(resolution,[status(thm)],[c_5872,c_6091])).

tff(c_6115,plain,(
    k9_subset_1(k2_struct_0('#skF_6'),'#skF_3'('#skF_5','#skF_7'),k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4573,c_6094])).

tff(c_6125,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_7'),u1_pre_topc('#skF_6'))
    | m1_pre_topc('#skF_7','#skF_5')
    | ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_6115])).

tff(c_6128,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_7'),u1_pre_topc('#skF_6'))
    | m1_pre_topc('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1180,c_268,c_6125])).

tff(c_6130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_5278,c_6128])).

tff(c_6131,plain,(
    k9_subset_1(k2_struct_0('#skF_6'),'#skF_3'('#skF_5','#skF_7'),k2_struct_0('#skF_6')) = '#skF_2'('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_6080])).

tff(c_696,plain,(
    ! [B_151,D_152,A_153] :
      ( r2_hidden(k9_subset_1(u1_struct_0(B_151),D_152,k2_struct_0(B_151)),u1_pre_topc(B_151))
      | ~ r2_hidden(D_152,u1_pre_topc(A_153))
      | ~ m1_subset_1(D_152,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_151),D_152,k2_struct_0(B_151)),k1_zfmisc_1(u1_struct_0(B_151)))
      | ~ m1_pre_topc(B_151,A_153)
      | ~ l1_pre_topc(B_151)
      | ~ l1_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_708,plain,(
    ! [B_151,D_152] :
      ( r2_hidden(k9_subset_1(u1_struct_0(B_151),D_152,k2_struct_0(B_151)),u1_pre_topc(B_151))
      | ~ r2_hidden(D_152,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(D_152,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_151),D_152,k2_struct_0(B_151)),k1_zfmisc_1(u1_struct_0(B_151)))
      | ~ m1_pre_topc(B_151,'#skF_4')
      | ~ l1_pre_topc(B_151)
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_696])).

tff(c_722,plain,(
    ! [B_154,D_155] :
      ( r2_hidden(k9_subset_1(u1_struct_0(B_154),D_155,k2_struct_0(B_154)),u1_pre_topc(B_154))
      | ~ r2_hidden(D_155,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(D_155,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_154),D_155,k2_struct_0(B_154)),k1_zfmisc_1(u1_struct_0(B_154)))
      | ~ m1_pre_topc(B_154,'#skF_4')
      | ~ l1_pre_topc(B_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_708])).

tff(c_755,plain,(
    ! [D_155] :
      ( r2_hidden(k9_subset_1(u1_struct_0('#skF_6'),D_155,k2_struct_0('#skF_6')),u1_pre_topc('#skF_6'))
      | ~ r2_hidden(D_155,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(D_155,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k9_subset_1(k2_struct_0('#skF_6'),D_155,k2_struct_0('#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_722])).

tff(c_776,plain,(
    ! [D_155] :
      ( r2_hidden(k9_subset_1(k2_struct_0('#skF_6'),D_155,k2_struct_0('#skF_6')),u1_pre_topc('#skF_6'))
      | ~ r2_hidden(D_155,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(D_155,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k9_subset_1(k2_struct_0('#skF_6'),D_155,k2_struct_0('#skF_6')),k1_zfmisc_1(k2_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44,c_76,c_76,c_755])).

tff(c_6138,plain,
    ( r2_hidden(k9_subset_1(k2_struct_0('#skF_6'),'#skF_3'('#skF_5','#skF_7'),k2_struct_0('#skF_6')),u1_pre_topc('#skF_6'))
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_7'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6131,c_776])).

tff(c_6151,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_7'),u1_pre_topc('#skF_6'))
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5872,c_4573,c_6131,c_6138])).

tff(c_6152,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_5278,c_6151])).

tff(c_6164,plain,
    ( m1_pre_topc('#skF_7','#skF_5')
    | ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_253,c_6152])).

tff(c_6167,plain,(
    m1_pre_topc('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1180,c_268,c_6164])).

tff(c_6169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_6167])).

tff(c_6171,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_7'),u1_pre_topc('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_5268])).

tff(c_6179,plain,(
    ! [D_703] :
      ( k9_subset_1(k2_struct_0('#skF_6'),D_703,k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden(D_703,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(D_703,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_5268])).

tff(c_6239,plain,(
    ! [B_712,C_713] :
      ( k9_subset_1(k2_struct_0('#skF_6'),'#skF_1'('#skF_4',B_712,C_713),k2_struct_0('#skF_6')) != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_4',B_712,C_713),u1_pre_topc('#skF_4'))
      | ~ r2_hidden(C_713,u1_pre_topc(B_712))
      | ~ m1_subset_1(C_713,k1_zfmisc_1(u1_struct_0(B_712)))
      | ~ m1_pre_topc(B_712,'#skF_4')
      | ~ l1_pre_topc(B_712) ) ),
    inference(resolution,[status(thm)],[c_487,c_6179])).

tff(c_6247,plain,(
    ! [C_132] :
      ( C_132 != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_4','#skF_6',C_132),u1_pre_topc('#skF_4'))
      | ~ r2_hidden(C_132,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | ~ l1_pre_topc('#skF_6')
      | ~ r2_hidden(C_132,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_struct_0('#skF_6')))
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_6239])).

tff(c_6253,plain,(
    ! [C_714] :
      ( C_714 != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_4','#skF_6',C_714),u1_pre_topc('#skF_4'))
      | ~ r2_hidden(C_714,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(C_714,k1_zfmisc_1(k2_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_44,c_52,c_44,c_76,c_6247])).

tff(c_6257,plain,(
    ! [C_35] :
      ( C_35 != '#skF_2'('#skF_5','#skF_7')
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_struct_0('#skF_6')))
      | ~ r2_hidden(C_35,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | ~ l1_pre_topc('#skF_6')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_6253])).

tff(c_6262,plain,(
    ! [C_715] :
      ( C_715 != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden(C_715,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(C_715,k1_zfmisc_1(k2_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_44,c_76,c_6257])).

tff(c_6287,plain,(
    ! [A_716] :
      ( '#skF_2'(A_716,'#skF_7') != '#skF_2'('#skF_5','#skF_7')
      | ~ r2_hidden('#skF_2'(A_716,'#skF_7'),u1_pre_topc('#skF_6'))
      | m1_pre_topc('#skF_7',A_716)
      | ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0(A_716))
      | ~ l1_pre_topc(A_716) ) ),
    inference(resolution,[status(thm)],[c_253,c_6262])).

tff(c_6290,plain,
    ( m1_pre_topc('#skF_7','#skF_5')
    | ~ r1_tarski(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_6171,c_6287])).

tff(c_6293,plain,(
    m1_pre_topc('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1180,c_268,c_6290])).

tff(c_6295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_6293])).

%------------------------------------------------------------------------------
