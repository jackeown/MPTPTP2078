%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:00 EST 2020

% Result     : Theorem 6.39s
% Output     : CNFRefutation 6.39s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 116 expanded)
%              Number of leaves         :   39 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :  151 ( 254 expanded)
%              Number of equality atoms :   19 (  32 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_mcart_1 > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_122,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_66,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_52,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_24,plain,(
    ! [A_29] :
      ( l1_struct_0(A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_54,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_46,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_104,plain,(
    ! [A_64] :
      ( v1_xboole_0(A_64)
      | r2_hidden('#skF_1'(A_64),A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_111,plain,(
    ! [A_64] :
      ( m1_subset_1('#skF_1'(A_64),A_64)
      | v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_104,c_14])).

tff(c_160,plain,(
    ! [A_77,B_78] :
      ( k6_domain_1(A_77,B_78) = k1_tarski(B_78)
      | ~ m1_subset_1(B_78,A_77)
      | v1_xboole_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_170,plain,(
    ! [A_64] :
      ( k6_domain_1(A_64,'#skF_1'(A_64)) = k1_tarski('#skF_1'(A_64))
      | v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_111,c_160])).

tff(c_303,plain,(
    ! [A_108,B_109] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_108),B_109),A_108)
      | ~ m1_subset_1(B_109,u1_struct_0(A_108))
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_4316,plain,(
    ! [A_277] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_277))),A_277)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_277)),u1_struct_0(A_277))
      | ~ l1_pre_topc(A_277)
      | ~ v2_pre_topc(A_277)
      | v2_struct_0(A_277)
      | v1_xboole_0(u1_struct_0(A_277)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_303])).

tff(c_50,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_76,plain,(
    ! [A_58] :
      ( r2_hidden('#skF_2'(A_58),A_58)
      | k1_xboole_0 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [A_59] :
      ( ~ v1_xboole_0(A_59)
      | k1_xboole_0 = A_59 ) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_85,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_81])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_70,plain,(
    ! [A_55,B_56] : k2_xboole_0(k1_tarski(A_55),B_56) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_74,plain,(
    ! [A_55] : k1_tarski(A_55) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_70])).

tff(c_93,plain,(
    ! [A_55] : k1_tarski(A_55) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_74])).

tff(c_207,plain,(
    ! [A_84,B_85] :
      ( m1_subset_1(k6_domain_1(A_84,B_85),k1_zfmisc_1(A_84))
      | ~ m1_subset_1(B_85,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_218,plain,(
    ! [A_64] :
      ( m1_subset_1(k1_tarski('#skF_1'(A_64)),k1_zfmisc_1(A_64))
      | ~ m1_subset_1('#skF_1'(A_64),A_64)
      | v1_xboole_0(A_64)
      | v1_xboole_0(A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_207])).

tff(c_12,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_95,plain,(
    ! [A_9] : m1_subset_1('#skF_5',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_12])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_97,plain,(
    ! [A_6] : r1_tarski('#skF_5',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_8])).

tff(c_722,plain,(
    ! [C_147,B_148,A_149] :
      ( C_147 = B_148
      | ~ r1_tarski(B_148,C_147)
      | ~ v2_tex_2(C_147,A_149)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ v3_tex_2(B_148,A_149)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_724,plain,(
    ! [A_6,A_149] :
      ( A_6 = '#skF_5'
      | ~ v2_tex_2(A_6,A_149)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ v3_tex_2('#skF_5',A_149)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149) ) ),
    inference(resolution,[status(thm)],[c_97,c_722])).

tff(c_728,plain,(
    ! [A_150,A_151] :
      ( A_150 = '#skF_5'
      | ~ v2_tex_2(A_150,A_151)
      | ~ m1_subset_1(A_150,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ v3_tex_2('#skF_5',A_151)
      | ~ l1_pre_topc(A_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_724])).

tff(c_751,plain,(
    ! [A_151] :
      ( k1_tarski('#skF_1'(u1_struct_0(A_151))) = '#skF_5'
      | ~ v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_151))),A_151)
      | ~ v3_tex_2('#skF_5',A_151)
      | ~ l1_pre_topc(A_151)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_151)),u1_struct_0(A_151))
      | v1_xboole_0(u1_struct_0(A_151)) ) ),
    inference(resolution,[status(thm)],[c_218,c_728])).

tff(c_791,plain,(
    ! [A_151] :
      ( ~ v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_151))),A_151)
      | ~ v3_tex_2('#skF_5',A_151)
      | ~ l1_pre_topc(A_151)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_151)),u1_struct_0(A_151))
      | v1_xboole_0(u1_struct_0(A_151)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_751])).

tff(c_4321,plain,(
    ! [A_278] :
      ( ~ v3_tex_2('#skF_5',A_278)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_278)),u1_struct_0(A_278))
      | ~ l1_pre_topc(A_278)
      | ~ v2_pre_topc(A_278)
      | v2_struct_0(A_278)
      | v1_xboole_0(u1_struct_0(A_278)) ) ),
    inference(resolution,[status(thm)],[c_4316,c_791])).

tff(c_4326,plain,(
    ! [A_279] :
      ( ~ v3_tex_2('#skF_5',A_279)
      | ~ l1_pre_topc(A_279)
      | ~ v2_pre_topc(A_279)
      | v2_struct_0(A_279)
      | v1_xboole_0(u1_struct_0(A_279)) ) ),
    inference(resolution,[status(thm)],[c_111,c_4321])).

tff(c_26,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(u1_struct_0(A_30))
      | ~ l1_struct_0(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4335,plain,(
    ! [A_280] :
      ( ~ l1_struct_0(A_280)
      | ~ v3_tex_2('#skF_5',A_280)
      | ~ l1_pre_topc(A_280)
      | ~ v2_pre_topc(A_280)
      | v2_struct_0(A_280) ) ),
    inference(resolution,[status(thm)],[c_4326,c_26])).

tff(c_4341,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_4335])).

tff(c_4345,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4341])).

tff(c_4346,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_4345])).

tff(c_4349,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_4346])).

tff(c_4353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4349])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:08:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.39/2.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.39/2.32  
% 6.39/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.39/2.33  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_mcart_1 > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 6.39/2.33  
% 6.39/2.33  %Foreground sorts:
% 6.39/2.33  
% 6.39/2.33  
% 6.39/2.33  %Background operators:
% 6.39/2.33  
% 6.39/2.33  
% 6.39/2.33  %Foreground operators:
% 6.39/2.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.39/2.33  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.39/2.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.39/2.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.39/2.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.39/2.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.39/2.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.39/2.33  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 6.39/2.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.39/2.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.39/2.33  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 6.39/2.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.39/2.33  tff('#skF_5', type, '#skF_5': $i).
% 6.39/2.33  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 6.39/2.33  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 6.39/2.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.39/2.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.39/2.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.39/2.33  tff('#skF_4', type, '#skF_4': $i).
% 6.39/2.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.39/2.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.39/2.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.39/2.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.39/2.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.39/2.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.39/2.33  
% 6.39/2.34  tff(f_138, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 6.39/2.34  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.39/2.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.39/2.34  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 6.39/2.34  tff(f_92, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 6.39/2.34  tff(f_122, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 6.39/2.34  tff(f_66, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 6.39/2.34  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 6.39/2.34  tff(f_38, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 6.39/2.34  tff(f_85, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 6.39/2.34  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 6.39/2.34  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.39/2.34  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 6.39/2.34  tff(f_78, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.39/2.34  tff(c_52, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.39/2.34  tff(c_24, plain, (![A_29]: (l1_struct_0(A_29) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.39/2.34  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.39/2.34  tff(c_54, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.39/2.34  tff(c_46, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.39/2.34  tff(c_104, plain, (![A_64]: (v1_xboole_0(A_64) | r2_hidden('#skF_1'(A_64), A_64))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.39/2.34  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.39/2.34  tff(c_111, plain, (![A_64]: (m1_subset_1('#skF_1'(A_64), A_64) | v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_104, c_14])).
% 6.39/2.34  tff(c_160, plain, (![A_77, B_78]: (k6_domain_1(A_77, B_78)=k1_tarski(B_78) | ~m1_subset_1(B_78, A_77) | v1_xboole_0(A_77))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.39/2.34  tff(c_170, plain, (![A_64]: (k6_domain_1(A_64, '#skF_1'(A_64))=k1_tarski('#skF_1'(A_64)) | v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_111, c_160])).
% 6.39/2.34  tff(c_303, plain, (![A_108, B_109]: (v2_tex_2(k6_domain_1(u1_struct_0(A_108), B_109), A_108) | ~m1_subset_1(B_109, u1_struct_0(A_108)) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.39/2.34  tff(c_4316, plain, (![A_277]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_277))), A_277) | ~m1_subset_1('#skF_1'(u1_struct_0(A_277)), u1_struct_0(A_277)) | ~l1_pre_topc(A_277) | ~v2_pre_topc(A_277) | v2_struct_0(A_277) | v1_xboole_0(u1_struct_0(A_277)))), inference(superposition, [status(thm), theory('equality')], [c_170, c_303])).
% 6.39/2.34  tff(c_50, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.39/2.34  tff(c_76, plain, (![A_58]: (r2_hidden('#skF_2'(A_58), A_58) | k1_xboole_0=A_58)), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.39/2.34  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.39/2.34  tff(c_81, plain, (![A_59]: (~v1_xboole_0(A_59) | k1_xboole_0=A_59)), inference(resolution, [status(thm)], [c_76, c_2])).
% 6.39/2.34  tff(c_85, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_81])).
% 6.39/2.34  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.39/2.34  tff(c_70, plain, (![A_55, B_56]: (k2_xboole_0(k1_tarski(A_55), B_56)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.39/2.34  tff(c_74, plain, (![A_55]: (k1_tarski(A_55)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_70])).
% 6.39/2.34  tff(c_93, plain, (![A_55]: (k1_tarski(A_55)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_74])).
% 6.39/2.34  tff(c_207, plain, (![A_84, B_85]: (m1_subset_1(k6_domain_1(A_84, B_85), k1_zfmisc_1(A_84)) | ~m1_subset_1(B_85, A_84) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.39/2.34  tff(c_218, plain, (![A_64]: (m1_subset_1(k1_tarski('#skF_1'(A_64)), k1_zfmisc_1(A_64)) | ~m1_subset_1('#skF_1'(A_64), A_64) | v1_xboole_0(A_64) | v1_xboole_0(A_64))), inference(superposition, [status(thm), theory('equality')], [c_170, c_207])).
% 6.39/2.34  tff(c_12, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.39/2.34  tff(c_95, plain, (![A_9]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_12])).
% 6.39/2.34  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.39/2.34  tff(c_97, plain, (![A_6]: (r1_tarski('#skF_5', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_8])).
% 6.39/2.34  tff(c_722, plain, (![C_147, B_148, A_149]: (C_147=B_148 | ~r1_tarski(B_148, C_147) | ~v2_tex_2(C_147, A_149) | ~m1_subset_1(C_147, k1_zfmisc_1(u1_struct_0(A_149))) | ~v3_tex_2(B_148, A_149) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.39/2.34  tff(c_724, plain, (![A_6, A_149]: (A_6='#skF_5' | ~v2_tex_2(A_6, A_149) | ~m1_subset_1(A_6, k1_zfmisc_1(u1_struct_0(A_149))) | ~v3_tex_2('#skF_5', A_149) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149))), inference(resolution, [status(thm)], [c_97, c_722])).
% 6.39/2.34  tff(c_728, plain, (![A_150, A_151]: (A_150='#skF_5' | ~v2_tex_2(A_150, A_151) | ~m1_subset_1(A_150, k1_zfmisc_1(u1_struct_0(A_151))) | ~v3_tex_2('#skF_5', A_151) | ~l1_pre_topc(A_151))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_724])).
% 6.39/2.34  tff(c_751, plain, (![A_151]: (k1_tarski('#skF_1'(u1_struct_0(A_151)))='#skF_5' | ~v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_151))), A_151) | ~v3_tex_2('#skF_5', A_151) | ~l1_pre_topc(A_151) | ~m1_subset_1('#skF_1'(u1_struct_0(A_151)), u1_struct_0(A_151)) | v1_xboole_0(u1_struct_0(A_151)))), inference(resolution, [status(thm)], [c_218, c_728])).
% 6.39/2.34  tff(c_791, plain, (![A_151]: (~v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_151))), A_151) | ~v3_tex_2('#skF_5', A_151) | ~l1_pre_topc(A_151) | ~m1_subset_1('#skF_1'(u1_struct_0(A_151)), u1_struct_0(A_151)) | v1_xboole_0(u1_struct_0(A_151)))), inference(negUnitSimplification, [status(thm)], [c_93, c_751])).
% 6.39/2.34  tff(c_4321, plain, (![A_278]: (~v3_tex_2('#skF_5', A_278) | ~m1_subset_1('#skF_1'(u1_struct_0(A_278)), u1_struct_0(A_278)) | ~l1_pre_topc(A_278) | ~v2_pre_topc(A_278) | v2_struct_0(A_278) | v1_xboole_0(u1_struct_0(A_278)))), inference(resolution, [status(thm)], [c_4316, c_791])).
% 6.39/2.34  tff(c_4326, plain, (![A_279]: (~v3_tex_2('#skF_5', A_279) | ~l1_pre_topc(A_279) | ~v2_pre_topc(A_279) | v2_struct_0(A_279) | v1_xboole_0(u1_struct_0(A_279)))), inference(resolution, [status(thm)], [c_111, c_4321])).
% 6.39/2.34  tff(c_26, plain, (![A_30]: (~v1_xboole_0(u1_struct_0(A_30)) | ~l1_struct_0(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.39/2.34  tff(c_4335, plain, (![A_280]: (~l1_struct_0(A_280) | ~v3_tex_2('#skF_5', A_280) | ~l1_pre_topc(A_280) | ~v2_pre_topc(A_280) | v2_struct_0(A_280))), inference(resolution, [status(thm)], [c_4326, c_26])).
% 6.39/2.34  tff(c_4341, plain, (~l1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_4335])).
% 6.39/2.34  tff(c_4345, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4341])).
% 6.39/2.34  tff(c_4346, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_4345])).
% 6.39/2.34  tff(c_4349, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_24, c_4346])).
% 6.39/2.34  tff(c_4353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_4349])).
% 6.39/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.39/2.34  
% 6.39/2.34  Inference rules
% 6.39/2.34  ----------------------
% 6.39/2.34  #Ref     : 0
% 6.39/2.34  #Sup     : 931
% 6.39/2.34  #Fact    : 0
% 6.39/2.34  #Define  : 0
% 6.39/2.34  #Split   : 14
% 6.39/2.34  #Chain   : 0
% 6.39/2.34  #Close   : 0
% 6.39/2.34  
% 6.39/2.34  Ordering : KBO
% 6.39/2.34  
% 6.39/2.34  Simplification rules
% 6.39/2.34  ----------------------
% 6.39/2.34  #Subsume      : 64
% 6.39/2.34  #Demod        : 1130
% 6.39/2.34  #Tautology    : 361
% 6.39/2.34  #SimpNegUnit  : 270
% 6.39/2.34  #BackRed      : 46
% 6.39/2.34  
% 6.39/2.34  #Partial instantiations: 0
% 6.39/2.34  #Strategies tried      : 1
% 6.39/2.34  
% 6.39/2.34  Timing (in seconds)
% 6.39/2.34  ----------------------
% 6.39/2.34  Preprocessing        : 0.33
% 6.39/2.34  Parsing              : 0.18
% 6.39/2.34  CNF conversion       : 0.02
% 6.39/2.34  Main loop            : 1.19
% 6.39/2.34  Inferencing          : 0.37
% 6.39/2.34  Reduction            : 0.38
% 6.39/2.34  Demodulation         : 0.25
% 6.39/2.34  BG Simplification    : 0.05
% 6.39/2.34  Subsumption          : 0.31
% 6.39/2.34  Abstraction          : 0.06
% 6.39/2.34  MUC search           : 0.00
% 6.39/2.34  Cooper               : 0.00
% 6.39/2.34  Total                : 1.55
% 6.39/2.34  Index Insertion      : 0.00
% 6.39/2.34  Index Deletion       : 0.00
% 6.39/2.34  Index Matching       : 0.00
% 6.39/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
