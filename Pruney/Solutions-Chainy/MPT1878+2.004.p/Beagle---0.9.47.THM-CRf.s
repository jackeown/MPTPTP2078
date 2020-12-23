%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:58 EST 2020

% Result     : Theorem 31.97s
% Output     : CNFRefutation 31.97s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 107 expanded)
%              Number of leaves         :   39 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  161 ( 239 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_133,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_60,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_121,axiom,(
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

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_60,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_58,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_52,plain,(
    v3_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_105,plain,(
    ! [A_59] :
      ( v1_xboole_0(A_59)
      | r2_hidden('#skF_1'(A_59),A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,B_23)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_112,plain,(
    ! [A_59] :
      ( m1_subset_1('#skF_1'(A_59),A_59)
      | v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_105,c_26])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_194,plain,(
    ! [A_78,B_79] :
      ( k6_domain_1(A_78,B_79) = k1_tarski(B_79)
      | ~ m1_subset_1(B_79,A_78)
      | v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_208,plain,(
    ! [A_59] :
      ( k6_domain_1(A_59,'#skF_1'(A_59)) = k1_tarski('#skF_1'(A_59))
      | v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_112,c_194])).

tff(c_574,plain,(
    ! [A_111,B_112] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_111),B_112),A_111)
      | ~ m1_subset_1(B_112,u1_struct_0(A_111))
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_18182,plain,(
    ! [A_582] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_582))),A_582)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_582)),u1_struct_0(A_582))
      | ~ l1_pre_topc(A_582)
      | ~ v2_pre_topc(A_582)
      | v2_struct_0(A_582)
      | v1_xboole_0(u1_struct_0(A_582)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_574])).

tff(c_56,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_64,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_56,c_64])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_76,plain,(
    ! [A_6] : k2_xboole_0(A_6,'#skF_6') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_8])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),B_9) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_98,plain,(
    ! [A_54,B_55] : k2_xboole_0(k1_tarski(A_54),B_55) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_12])).

tff(c_102,plain,(
    ! [A_54] : k1_tarski(A_54) != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_98])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k1_tarski(A_17),k1_zfmisc_1(B_18))
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [A_16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_86,plain,(
    ! [A_16] : m1_subset_1('#skF_6',k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_20])).

tff(c_10,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_70,plain,(
    ! [A_7] : r1_tarski('#skF_6',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_10])).

tff(c_935,plain,(
    ! [C_133,B_134,A_135] :
      ( C_133 = B_134
      | ~ r1_tarski(B_134,C_133)
      | ~ v2_tex_2(C_133,A_135)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ v3_tex_2(B_134,A_135)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_937,plain,(
    ! [A_7,A_135] :
      ( A_7 = '#skF_6'
      | ~ v2_tex_2(A_7,A_135)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ v3_tex_2('#skF_6',A_135)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(resolution,[status(thm)],[c_70,c_935])).

tff(c_1839,plain,(
    ! [A_198,A_199] :
      ( A_198 = '#skF_6'
      | ~ v2_tex_2(A_198,A_199)
      | ~ m1_subset_1(A_198,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ v3_tex_2('#skF_6',A_199)
      | ~ l1_pre_topc(A_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_937])).

tff(c_1869,plain,(
    ! [A_17,A_199] :
      ( k1_tarski(A_17) = '#skF_6'
      | ~ v2_tex_2(k1_tarski(A_17),A_199)
      | ~ v3_tex_2('#skF_6',A_199)
      | ~ l1_pre_topc(A_199)
      | ~ r2_hidden(A_17,u1_struct_0(A_199)) ) ),
    inference(resolution,[status(thm)],[c_22,c_1839])).

tff(c_1891,plain,(
    ! [A_17,A_199] :
      ( ~ v2_tex_2(k1_tarski(A_17),A_199)
      | ~ v3_tex_2('#skF_6',A_199)
      | ~ l1_pre_topc(A_199)
      | ~ r2_hidden(A_17,u1_struct_0(A_199)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_1869])).

tff(c_66944,plain,(
    ! [A_1148] :
      ( ~ v3_tex_2('#skF_6',A_1148)
      | ~ r2_hidden('#skF_1'(u1_struct_0(A_1148)),u1_struct_0(A_1148))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_1148)),u1_struct_0(A_1148))
      | ~ l1_pre_topc(A_1148)
      | ~ v2_pre_topc(A_1148)
      | v2_struct_0(A_1148)
      | v1_xboole_0(u1_struct_0(A_1148)) ) ),
    inference(resolution,[status(thm)],[c_18182,c_1891])).

tff(c_66958,plain,(
    ! [A_1149] :
      ( ~ v3_tex_2('#skF_6',A_1149)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_1149)),u1_struct_0(A_1149))
      | ~ l1_pre_topc(A_1149)
      | ~ v2_pre_topc(A_1149)
      | v2_struct_0(A_1149)
      | v1_xboole_0(u1_struct_0(A_1149)) ) ),
    inference(resolution,[status(thm)],[c_4,c_66944])).

tff(c_66982,plain,(
    ! [A_1150] :
      ( ~ v3_tex_2('#skF_6',A_1150)
      | ~ l1_pre_topc(A_1150)
      | ~ v2_pre_topc(A_1150)
      | v2_struct_0(A_1150)
      | v1_xboole_0(u1_struct_0(A_1150)) ) ),
    inference(resolution,[status(thm)],[c_112,c_66958])).

tff(c_288,plain,(
    ! [A_92] :
      ( m1_subset_1('#skF_3'(A_92),k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    ! [B_21,A_19] :
      ( v1_xboole_0(B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_19))
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_299,plain,(
    ! [A_92] :
      ( v1_xboole_0('#skF_3'(A_92))
      | ~ v1_xboole_0(u1_struct_0(A_92))
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(resolution,[status(thm)],[c_288,c_24])).

tff(c_66999,plain,(
    ! [A_1151] :
      ( v1_xboole_0('#skF_3'(A_1151))
      | ~ v3_tex_2('#skF_6',A_1151)
      | ~ l1_pre_topc(A_1151)
      | ~ v2_pre_topc(A_1151)
      | v2_struct_0(A_1151) ) ),
    inference(resolution,[status(thm)],[c_66982,c_299])).

tff(c_32,plain,(
    ! [A_27] :
      ( ~ v1_xboole_0('#skF_3'(A_27))
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_67012,plain,(
    ! [A_1152] :
      ( ~ v3_tex_2('#skF_6',A_1152)
      | ~ l1_pre_topc(A_1152)
      | ~ v2_pre_topc(A_1152)
      | v2_struct_0(A_1152) ) ),
    inference(resolution,[status(thm)],[c_66999,c_32])).

tff(c_67018,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_67012])).

tff(c_67022,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_67018])).

tff(c_67024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_67022])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:15:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 31.97/21.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.97/21.98  
% 31.97/21.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.97/21.98  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 31.97/21.98  
% 31.97/21.98  %Foreground sorts:
% 31.97/21.98  
% 31.97/21.98  
% 31.97/21.98  %Background operators:
% 31.97/21.98  
% 31.97/21.98  
% 31.97/21.98  %Foreground operators:
% 31.97/21.98  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 31.97/21.98  tff('#skF_2', type, '#skF_2': $i > $i).
% 31.97/21.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 31.97/21.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 31.97/21.98  tff(k1_tarski, type, k1_tarski: $i > $i).
% 31.97/21.98  tff('#skF_1', type, '#skF_1': $i > $i).
% 31.97/21.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 31.97/21.98  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 31.97/21.98  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 31.97/21.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 31.97/21.98  tff('#skF_5', type, '#skF_5': $i).
% 31.97/21.98  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 31.97/21.98  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 31.97/21.98  tff('#skF_6', type, '#skF_6': $i).
% 31.97/21.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 31.97/21.98  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 31.97/21.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 31.97/21.98  tff('#skF_3', type, '#skF_3': $i > $i).
% 31.97/21.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 31.97/21.98  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 31.97/21.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 31.97/21.98  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 31.97/21.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 31.97/21.98  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 31.97/21.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 31.97/21.98  
% 31.97/22.00  tff(f_149, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 31.97/22.00  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 31.97/22.00  tff(f_75, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 31.97/22.00  tff(f_103, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 31.97/22.00  tff(f_133, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 31.97/22.00  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 31.97/22.00  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 31.97/22.00  tff(f_42, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 31.97/22.00  tff(f_64, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 31.97/22.00  tff(f_60, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 31.97/22.00  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 31.97/22.00  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 31.97/22.00  tff(f_96, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_pre_topc)).
% 31.97/22.00  tff(f_71, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 31.97/22.00  tff(c_62, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 31.97/22.00  tff(c_60, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 31.97/22.00  tff(c_58, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 31.97/22.00  tff(c_52, plain, (v3_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 31.97/22.00  tff(c_105, plain, (![A_59]: (v1_xboole_0(A_59) | r2_hidden('#skF_1'(A_59), A_59))), inference(cnfTransformation, [status(thm)], [f_31])).
% 31.97/22.00  tff(c_26, plain, (![A_22, B_23]: (m1_subset_1(A_22, B_23) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 31.97/22.00  tff(c_112, plain, (![A_59]: (m1_subset_1('#skF_1'(A_59), A_59) | v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_105, c_26])).
% 31.97/22.00  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 31.97/22.00  tff(c_194, plain, (![A_78, B_79]: (k6_domain_1(A_78, B_79)=k1_tarski(B_79) | ~m1_subset_1(B_79, A_78) | v1_xboole_0(A_78))), inference(cnfTransformation, [status(thm)], [f_103])).
% 31.97/22.00  tff(c_208, plain, (![A_59]: (k6_domain_1(A_59, '#skF_1'(A_59))=k1_tarski('#skF_1'(A_59)) | v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_112, c_194])).
% 31.97/22.00  tff(c_574, plain, (![A_111, B_112]: (v2_tex_2(k6_domain_1(u1_struct_0(A_111), B_112), A_111) | ~m1_subset_1(B_112, u1_struct_0(A_111)) | ~l1_pre_topc(A_111) | ~v2_pre_topc(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_133])).
% 31.97/22.00  tff(c_18182, plain, (![A_582]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_582))), A_582) | ~m1_subset_1('#skF_1'(u1_struct_0(A_582)), u1_struct_0(A_582)) | ~l1_pre_topc(A_582) | ~v2_pre_topc(A_582) | v2_struct_0(A_582) | v1_xboole_0(u1_struct_0(A_582)))), inference(superposition, [status(thm), theory('equality')], [c_208, c_574])).
% 31.97/22.00  tff(c_56, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 31.97/22.00  tff(c_64, plain, (![A_46]: (k1_xboole_0=A_46 | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_35])).
% 31.97/22.00  tff(c_68, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_56, c_64])).
% 31.97/22.00  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 31.97/22.00  tff(c_76, plain, (![A_6]: (k2_xboole_0(A_6, '#skF_6')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_8])).
% 31.97/22.00  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 31.97/22.00  tff(c_98, plain, (![A_54, B_55]: (k2_xboole_0(k1_tarski(A_54), B_55)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_12])).
% 31.97/22.00  tff(c_102, plain, (![A_54]: (k1_tarski(A_54)!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_76, c_98])).
% 31.97/22.00  tff(c_22, plain, (![A_17, B_18]: (m1_subset_1(k1_tarski(A_17), k1_zfmisc_1(B_18)) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 31.97/22.00  tff(c_20, plain, (![A_16]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 31.97/22.00  tff(c_86, plain, (![A_16]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_20])).
% 31.97/22.00  tff(c_10, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 31.97/22.00  tff(c_70, plain, (![A_7]: (r1_tarski('#skF_6', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_10])).
% 31.97/22.00  tff(c_935, plain, (![C_133, B_134, A_135]: (C_133=B_134 | ~r1_tarski(B_134, C_133) | ~v2_tex_2(C_133, A_135) | ~m1_subset_1(C_133, k1_zfmisc_1(u1_struct_0(A_135))) | ~v3_tex_2(B_134, A_135) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_121])).
% 31.97/22.00  tff(c_937, plain, (![A_7, A_135]: (A_7='#skF_6' | ~v2_tex_2(A_7, A_135) | ~m1_subset_1(A_7, k1_zfmisc_1(u1_struct_0(A_135))) | ~v3_tex_2('#skF_6', A_135) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(resolution, [status(thm)], [c_70, c_935])).
% 31.97/22.00  tff(c_1839, plain, (![A_198, A_199]: (A_198='#skF_6' | ~v2_tex_2(A_198, A_199) | ~m1_subset_1(A_198, k1_zfmisc_1(u1_struct_0(A_199))) | ~v3_tex_2('#skF_6', A_199) | ~l1_pre_topc(A_199))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_937])).
% 31.97/22.00  tff(c_1869, plain, (![A_17, A_199]: (k1_tarski(A_17)='#skF_6' | ~v2_tex_2(k1_tarski(A_17), A_199) | ~v3_tex_2('#skF_6', A_199) | ~l1_pre_topc(A_199) | ~r2_hidden(A_17, u1_struct_0(A_199)))), inference(resolution, [status(thm)], [c_22, c_1839])).
% 31.97/22.00  tff(c_1891, plain, (![A_17, A_199]: (~v2_tex_2(k1_tarski(A_17), A_199) | ~v3_tex_2('#skF_6', A_199) | ~l1_pre_topc(A_199) | ~r2_hidden(A_17, u1_struct_0(A_199)))), inference(negUnitSimplification, [status(thm)], [c_102, c_1869])).
% 31.97/22.00  tff(c_66944, plain, (![A_1148]: (~v3_tex_2('#skF_6', A_1148) | ~r2_hidden('#skF_1'(u1_struct_0(A_1148)), u1_struct_0(A_1148)) | ~m1_subset_1('#skF_1'(u1_struct_0(A_1148)), u1_struct_0(A_1148)) | ~l1_pre_topc(A_1148) | ~v2_pre_topc(A_1148) | v2_struct_0(A_1148) | v1_xboole_0(u1_struct_0(A_1148)))), inference(resolution, [status(thm)], [c_18182, c_1891])).
% 31.97/22.00  tff(c_66958, plain, (![A_1149]: (~v3_tex_2('#skF_6', A_1149) | ~m1_subset_1('#skF_1'(u1_struct_0(A_1149)), u1_struct_0(A_1149)) | ~l1_pre_topc(A_1149) | ~v2_pre_topc(A_1149) | v2_struct_0(A_1149) | v1_xboole_0(u1_struct_0(A_1149)))), inference(resolution, [status(thm)], [c_4, c_66944])).
% 31.97/22.00  tff(c_66982, plain, (![A_1150]: (~v3_tex_2('#skF_6', A_1150) | ~l1_pre_topc(A_1150) | ~v2_pre_topc(A_1150) | v2_struct_0(A_1150) | v1_xboole_0(u1_struct_0(A_1150)))), inference(resolution, [status(thm)], [c_112, c_66958])).
% 31.97/22.00  tff(c_288, plain, (![A_92]: (m1_subset_1('#skF_3'(A_92), k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_96])).
% 31.97/22.00  tff(c_24, plain, (![B_21, A_19]: (v1_xboole_0(B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(A_19)) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 31.97/22.00  tff(c_299, plain, (![A_92]: (v1_xboole_0('#skF_3'(A_92)) | ~v1_xboole_0(u1_struct_0(A_92)) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92))), inference(resolution, [status(thm)], [c_288, c_24])).
% 31.97/22.00  tff(c_66999, plain, (![A_1151]: (v1_xboole_0('#skF_3'(A_1151)) | ~v3_tex_2('#skF_6', A_1151) | ~l1_pre_topc(A_1151) | ~v2_pre_topc(A_1151) | v2_struct_0(A_1151))), inference(resolution, [status(thm)], [c_66982, c_299])).
% 31.97/22.00  tff(c_32, plain, (![A_27]: (~v1_xboole_0('#skF_3'(A_27)) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_96])).
% 31.97/22.00  tff(c_67012, plain, (![A_1152]: (~v3_tex_2('#skF_6', A_1152) | ~l1_pre_topc(A_1152) | ~v2_pre_topc(A_1152) | v2_struct_0(A_1152))), inference(resolution, [status(thm)], [c_66999, c_32])).
% 31.97/22.00  tff(c_67018, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_52, c_67012])).
% 31.97/22.00  tff(c_67022, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_67018])).
% 31.97/22.00  tff(c_67024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_67022])).
% 31.97/22.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.97/22.00  
% 31.97/22.00  Inference rules
% 31.97/22.00  ----------------------
% 31.97/22.00  #Ref     : 0
% 31.97/22.00  #Sup     : 16038
% 31.97/22.00  #Fact    : 0
% 31.97/22.00  #Define  : 0
% 31.97/22.00  #Split   : 20
% 31.97/22.00  #Chain   : 0
% 31.97/22.00  #Close   : 0
% 31.97/22.00  
% 31.97/22.00  Ordering : KBO
% 31.97/22.00  
% 31.97/22.00  Simplification rules
% 31.97/22.00  ----------------------
% 31.97/22.00  #Subsume      : 4763
% 31.97/22.00  #Demod        : 7962
% 31.97/22.00  #Tautology    : 1931
% 31.97/22.00  #SimpNegUnit  : 937
% 31.97/22.00  #BackRed      : 53
% 31.97/22.00  
% 31.97/22.00  #Partial instantiations: 0
% 31.97/22.00  #Strategies tried      : 1
% 31.97/22.00  
% 31.97/22.00  Timing (in seconds)
% 31.97/22.00  ----------------------
% 31.97/22.00  Preprocessing        : 0.35
% 31.97/22.00  Parsing              : 0.18
% 31.97/22.00  CNF conversion       : 0.03
% 31.97/22.00  Main loop            : 20.88
% 31.97/22.00  Inferencing          : 2.16
% 31.97/22.00  Reduction            : 3.45
% 31.97/22.00  Demodulation         : 2.32
% 31.97/22.00  BG Simplification    : 0.29
% 31.97/22.00  Subsumption          : 13.90
% 31.97/22.00  Abstraction          : 0.48
% 31.97/22.00  MUC search           : 0.00
% 31.97/22.00  Cooper               : 0.00
% 31.97/22.00  Total                : 21.26
% 31.97/22.00  Index Insertion      : 0.00
% 31.97/22.00  Index Deletion       : 0.00
% 31.97/22.00  Index Matching       : 0.00
% 31.97/22.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
