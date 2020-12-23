%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:03 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 138 expanded)
%              Number of leaves         :   37 (  62 expanded)
%              Depth                    :   19
%              Number of atoms          :  161 ( 310 expanded)
%              Number of equality atoms :   33 (  62 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_40,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_98,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_22,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_46,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_42,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_54,plain,(
    ! [A_35] :
      ( k1_xboole_0 = A_35
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_63,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_54])).

tff(c_6,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_100,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | A_2 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_6])).

tff(c_102,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(A_45,B_46)
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_106,plain,(
    ! [A_2] :
      ( m1_subset_1('#skF_1'(A_2),A_2)
      | A_2 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_100,c_102])).

tff(c_127,plain,(
    ! [A_56,B_57] :
      ( k6_domain_1(A_56,B_57) = k1_tarski(B_57)
      | ~ m1_subset_1(B_57,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_205,plain,(
    ! [A_72] :
      ( k6_domain_1(A_72,'#skF_1'(A_72)) = k1_tarski('#skF_1'(A_72))
      | v1_xboole_0(A_72)
      | A_72 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_106,c_127])).

tff(c_40,plain,(
    ! [A_30,B_32] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_30),B_32),A_30)
      | ~ m1_subset_1(B_32,u1_struct_0(A_30))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_586,plain,(
    ! [A_134] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_134))),A_134)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_134)),u1_struct_0(A_134))
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134)
      | v1_xboole_0(u1_struct_0(A_134))
      | u1_struct_0(A_134) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_40])).

tff(c_8,plain,(
    ! [A_4] : k2_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_76,plain,(
    ! [A_4] : k2_xboole_0(A_4,'#skF_4') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_8])).

tff(c_12,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),B_7) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_94,plain,(
    ! [A_41,B_42] : k2_xboole_0(k1_tarski(A_41),B_42) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_12])).

tff(c_98,plain,(
    ! [A_41] : k1_tarski(A_41) != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_94])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k1_tarski(A_9),k1_zfmisc_1(B_10))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_73,plain,(
    ! [A_8] : m1_subset_1('#skF_4',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_14])).

tff(c_10,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_10])).

tff(c_429,plain,(
    ! [C_110,B_111,A_112] :
      ( C_110 = B_111
      | ~ r1_tarski(B_111,C_110)
      | ~ v2_tex_2(C_110,A_112)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ v3_tex_2(B_111,A_112)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_433,plain,(
    ! [A_5,A_112] :
      ( A_5 = '#skF_4'
      | ~ v2_tex_2(A_5,A_112)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ v3_tex_2('#skF_4',A_112)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(resolution,[status(thm)],[c_65,c_429])).

tff(c_438,plain,(
    ! [A_113,A_114] :
      ( A_113 = '#skF_4'
      | ~ v2_tex_2(A_113,A_114)
      | ~ m1_subset_1(A_113,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ v3_tex_2('#skF_4',A_114)
      | ~ l1_pre_topc(A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_433])).

tff(c_457,plain,(
    ! [A_9,A_114] :
      ( k1_tarski(A_9) = '#skF_4'
      | ~ v2_tex_2(k1_tarski(A_9),A_114)
      | ~ v3_tex_2('#skF_4',A_114)
      | ~ l1_pre_topc(A_114)
      | ~ r2_hidden(A_9,u1_struct_0(A_114)) ) ),
    inference(resolution,[status(thm)],[c_16,c_438])).

tff(c_472,plain,(
    ! [A_9,A_114] :
      ( ~ v2_tex_2(k1_tarski(A_9),A_114)
      | ~ v3_tex_2('#skF_4',A_114)
      | ~ l1_pre_topc(A_114)
      | ~ r2_hidden(A_9,u1_struct_0(A_114)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_457])).

tff(c_632,plain,(
    ! [A_153] :
      ( ~ v3_tex_2('#skF_4',A_153)
      | ~ r2_hidden('#skF_1'(u1_struct_0(A_153)),u1_struct_0(A_153))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_153)),u1_struct_0(A_153))
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153)
      | v1_xboole_0(u1_struct_0(A_153))
      | u1_struct_0(A_153) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_586,c_472])).

tff(c_637,plain,(
    ! [A_154] :
      ( ~ v3_tex_2('#skF_4',A_154)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_154)),u1_struct_0(A_154))
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154)
      | v1_xboole_0(u1_struct_0(A_154))
      | u1_struct_0(A_154) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_100,c_632])).

tff(c_647,plain,(
    ! [A_156] :
      ( ~ v3_tex_2('#skF_4',A_156)
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156)
      | v1_xboole_0(u1_struct_0(A_156))
      | u1_struct_0(A_156) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_106,c_637])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_64,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_4])).

tff(c_656,plain,(
    ! [A_157] :
      ( ~ v3_tex_2('#skF_4',A_157)
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157)
      | u1_struct_0(A_157) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_647,c_64])).

tff(c_662,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_656])).

tff(c_666,plain,
    ( v2_struct_0('#skF_3')
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_662])).

tff(c_667,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_666])).

tff(c_24,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_711,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_667,c_24])).

tff(c_745,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_711])).

tff(c_746,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_745])).

tff(c_750,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_746])).

tff(c_754,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_750])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.54  
% 3.24/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.54  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.24/1.54  
% 3.24/1.54  %Foreground sorts:
% 3.24/1.54  
% 3.24/1.54  
% 3.24/1.54  %Background operators:
% 3.24/1.54  
% 3.24/1.54  
% 3.24/1.54  %Foreground operators:
% 3.24/1.54  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.24/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.24/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.24/1.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.24/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.24/1.54  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.24/1.54  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.24/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.24/1.54  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.24/1.54  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.24/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.24/1.54  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.24/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.24/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.24/1.54  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.24/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.24/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.24/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.24/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.24/1.54  
% 3.40/1.56  tff(f_126, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 3.40/1.56  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.40/1.56  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.40/1.56  tff(f_38, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.40/1.56  tff(f_55, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.40/1.56  tff(f_80, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.40/1.56  tff(f_110, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 3.40/1.56  tff(f_40, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.40/1.56  tff(f_45, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.40/1.56  tff(f_51, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 3.40/1.56  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.40/1.56  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.40/1.56  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 3.40/1.56  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.40/1.56  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.40/1.56  tff(c_22, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.40/1.56  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.40/1.56  tff(c_46, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.40/1.56  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.40/1.56  tff(c_42, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.40/1.56  tff(c_54, plain, (![A_35]: (k1_xboole_0=A_35 | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.40/1.56  tff(c_63, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_46, c_54])).
% 3.40/1.56  tff(c_6, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.40/1.56  tff(c_100, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | A_2='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_6])).
% 3.40/1.56  tff(c_102, plain, (![A_45, B_46]: (m1_subset_1(A_45, B_46) | ~r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.40/1.56  tff(c_106, plain, (![A_2]: (m1_subset_1('#skF_1'(A_2), A_2) | A_2='#skF_4')), inference(resolution, [status(thm)], [c_100, c_102])).
% 3.40/1.56  tff(c_127, plain, (![A_56, B_57]: (k6_domain_1(A_56, B_57)=k1_tarski(B_57) | ~m1_subset_1(B_57, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.40/1.56  tff(c_205, plain, (![A_72]: (k6_domain_1(A_72, '#skF_1'(A_72))=k1_tarski('#skF_1'(A_72)) | v1_xboole_0(A_72) | A_72='#skF_4')), inference(resolution, [status(thm)], [c_106, c_127])).
% 3.40/1.56  tff(c_40, plain, (![A_30, B_32]: (v2_tex_2(k6_domain_1(u1_struct_0(A_30), B_32), A_30) | ~m1_subset_1(B_32, u1_struct_0(A_30)) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.40/1.56  tff(c_586, plain, (![A_134]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_134))), A_134) | ~m1_subset_1('#skF_1'(u1_struct_0(A_134)), u1_struct_0(A_134)) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134) | v1_xboole_0(u1_struct_0(A_134)) | u1_struct_0(A_134)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_205, c_40])).
% 3.40/1.56  tff(c_8, plain, (![A_4]: (k2_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.40/1.56  tff(c_76, plain, (![A_4]: (k2_xboole_0(A_4, '#skF_4')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_63, c_8])).
% 3.40/1.56  tff(c_12, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.40/1.56  tff(c_94, plain, (![A_41, B_42]: (k2_xboole_0(k1_tarski(A_41), B_42)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_12])).
% 3.40/1.56  tff(c_98, plain, (![A_41]: (k1_tarski(A_41)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_76, c_94])).
% 3.40/1.56  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(k1_tarski(A_9), k1_zfmisc_1(B_10)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.40/1.56  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.40/1.56  tff(c_73, plain, (![A_8]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_14])).
% 3.40/1.56  tff(c_10, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.40/1.56  tff(c_65, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_10])).
% 3.40/1.56  tff(c_429, plain, (![C_110, B_111, A_112]: (C_110=B_111 | ~r1_tarski(B_111, C_110) | ~v2_tex_2(C_110, A_112) | ~m1_subset_1(C_110, k1_zfmisc_1(u1_struct_0(A_112))) | ~v3_tex_2(B_111, A_112) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.40/1.56  tff(c_433, plain, (![A_5, A_112]: (A_5='#skF_4' | ~v2_tex_2(A_5, A_112) | ~m1_subset_1(A_5, k1_zfmisc_1(u1_struct_0(A_112))) | ~v3_tex_2('#skF_4', A_112) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(resolution, [status(thm)], [c_65, c_429])).
% 3.40/1.56  tff(c_438, plain, (![A_113, A_114]: (A_113='#skF_4' | ~v2_tex_2(A_113, A_114) | ~m1_subset_1(A_113, k1_zfmisc_1(u1_struct_0(A_114))) | ~v3_tex_2('#skF_4', A_114) | ~l1_pre_topc(A_114))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_433])).
% 3.40/1.56  tff(c_457, plain, (![A_9, A_114]: (k1_tarski(A_9)='#skF_4' | ~v2_tex_2(k1_tarski(A_9), A_114) | ~v3_tex_2('#skF_4', A_114) | ~l1_pre_topc(A_114) | ~r2_hidden(A_9, u1_struct_0(A_114)))), inference(resolution, [status(thm)], [c_16, c_438])).
% 3.40/1.56  tff(c_472, plain, (![A_9, A_114]: (~v2_tex_2(k1_tarski(A_9), A_114) | ~v3_tex_2('#skF_4', A_114) | ~l1_pre_topc(A_114) | ~r2_hidden(A_9, u1_struct_0(A_114)))), inference(negUnitSimplification, [status(thm)], [c_98, c_457])).
% 3.40/1.56  tff(c_632, plain, (![A_153]: (~v3_tex_2('#skF_4', A_153) | ~r2_hidden('#skF_1'(u1_struct_0(A_153)), u1_struct_0(A_153)) | ~m1_subset_1('#skF_1'(u1_struct_0(A_153)), u1_struct_0(A_153)) | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153) | v2_struct_0(A_153) | v1_xboole_0(u1_struct_0(A_153)) | u1_struct_0(A_153)='#skF_4')), inference(resolution, [status(thm)], [c_586, c_472])).
% 3.40/1.56  tff(c_637, plain, (![A_154]: (~v3_tex_2('#skF_4', A_154) | ~m1_subset_1('#skF_1'(u1_struct_0(A_154)), u1_struct_0(A_154)) | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154) | v1_xboole_0(u1_struct_0(A_154)) | u1_struct_0(A_154)='#skF_4')), inference(resolution, [status(thm)], [c_100, c_632])).
% 3.40/1.56  tff(c_647, plain, (![A_156]: (~v3_tex_2('#skF_4', A_156) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156) | v1_xboole_0(u1_struct_0(A_156)) | u1_struct_0(A_156)='#skF_4')), inference(resolution, [status(thm)], [c_106, c_637])).
% 3.40/1.56  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.40/1.56  tff(c_64, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_4])).
% 3.40/1.56  tff(c_656, plain, (![A_157]: (~v3_tex_2('#skF_4', A_157) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157) | u1_struct_0(A_157)='#skF_4')), inference(resolution, [status(thm)], [c_647, c_64])).
% 3.40/1.56  tff(c_662, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_42, c_656])).
% 3.40/1.56  tff(c_666, plain, (v2_struct_0('#skF_3') | u1_struct_0('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_662])).
% 3.40/1.56  tff(c_667, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_666])).
% 3.40/1.56  tff(c_24, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.40/1.56  tff(c_711, plain, (~v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_667, c_24])).
% 3.40/1.56  tff(c_745, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_711])).
% 3.40/1.56  tff(c_746, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_745])).
% 3.40/1.56  tff(c_750, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_22, c_746])).
% 3.40/1.56  tff(c_754, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_750])).
% 3.40/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.56  
% 3.40/1.56  Inference rules
% 3.40/1.56  ----------------------
% 3.40/1.56  #Ref     : 0
% 3.40/1.56  #Sup     : 143
% 3.40/1.56  #Fact    : 0
% 3.40/1.56  #Define  : 0
% 3.40/1.56  #Split   : 0
% 3.40/1.56  #Chain   : 0
% 3.40/1.56  #Close   : 0
% 3.40/1.56  
% 3.40/1.56  Ordering : KBO
% 3.40/1.56  
% 3.40/1.56  Simplification rules
% 3.40/1.56  ----------------------
% 3.40/1.56  #Subsume      : 5
% 3.40/1.56  #Demod        : 56
% 3.40/1.56  #Tautology    : 37
% 3.40/1.56  #SimpNegUnit  : 8
% 3.40/1.56  #BackRed      : 3
% 3.40/1.56  
% 3.40/1.56  #Partial instantiations: 0
% 3.40/1.56  #Strategies tried      : 1
% 3.40/1.56  
% 3.40/1.56  Timing (in seconds)
% 3.40/1.56  ----------------------
% 3.40/1.56  Preprocessing        : 0.32
% 3.40/1.56  Parsing              : 0.16
% 3.40/1.56  CNF conversion       : 0.02
% 3.40/1.56  Main loop            : 0.40
% 3.40/1.56  Inferencing          : 0.16
% 3.40/1.56  Reduction            : 0.11
% 3.40/1.56  Demodulation         : 0.07
% 3.40/1.56  BG Simplification    : 0.02
% 3.40/1.56  Subsumption          : 0.08
% 3.40/1.56  Abstraction          : 0.02
% 3.40/1.56  MUC search           : 0.00
% 3.40/1.56  Cooper               : 0.00
% 3.40/1.56  Total                : 0.75
% 3.40/1.56  Index Insertion      : 0.00
% 3.40/1.56  Index Deletion       : 0.00
% 3.40/1.56  Index Matching       : 0.00
% 3.40/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
