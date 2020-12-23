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
% DateTime   : Thu Dec  3 10:30:00 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 5.00s
% Verified   : 
% Statistics : Number of formulae       :   71 (  89 expanded)
%              Number of leaves         :   35 (  45 expanded)
%              Depth                    :   17
%              Number of atoms          :  146 ( 206 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_109,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_97,axiom,(
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

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_20,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_42,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_46,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(A_45,B_46)
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_95,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_91])).

tff(c_40,plain,(
    ! [A_30,B_32] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_30),B_32),A_30)
      | ~ m1_subset_1(B_32,u1_struct_0(A_30))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k6_domain_1(A_16,B_17),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_57,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_57])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_68,plain,(
    ! [A_8] : m1_subset_1('#skF_4',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_14])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_10])).

tff(c_549,plain,(
    ! [C_95,B_96,A_97] :
      ( C_95 = B_96
      | ~ r1_tarski(B_96,C_95)
      | ~ v2_tex_2(C_95,A_97)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ v3_tex_2(B_96,A_97)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_551,plain,(
    ! [A_6,A_97] :
      ( A_6 = '#skF_4'
      | ~ v2_tex_2(A_6,A_97)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ v3_tex_2('#skF_4',A_97)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_69,c_549])).

tff(c_754,plain,(
    ! [A_105,A_106] :
      ( A_105 = '#skF_4'
      | ~ v2_tex_2(A_105,A_106)
      | ~ m1_subset_1(A_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ v3_tex_2('#skF_4',A_106)
      | ~ l1_pre_topc(A_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_551])).

tff(c_2268,plain,(
    ! [A_165,B_166] :
      ( k6_domain_1(u1_struct_0(A_165),B_166) = '#skF_4'
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_165),B_166),A_165)
      | ~ v3_tex_2('#skF_4',A_165)
      | ~ l1_pre_topc(A_165)
      | ~ m1_subset_1(B_166,u1_struct_0(A_165))
      | v1_xboole_0(u1_struct_0(A_165)) ) ),
    inference(resolution,[status(thm)],[c_24,c_754])).

tff(c_2289,plain,(
    ! [A_167,B_168] :
      ( k6_domain_1(u1_struct_0(A_167),B_168) = '#skF_4'
      | ~ v3_tex_2('#skF_4',A_167)
      | v1_xboole_0(u1_struct_0(A_167))
      | ~ m1_subset_1(B_168,u1_struct_0(A_167))
      | ~ l1_pre_topc(A_167)
      | ~ v2_pre_topc(A_167)
      | v2_struct_0(A_167) ) ),
    inference(resolution,[status(thm)],[c_40,c_2268])).

tff(c_2315,plain,(
    ! [A_169] :
      ( k6_domain_1(u1_struct_0(A_169),'#skF_1'(u1_struct_0(A_169))) = '#skF_4'
      | ~ v3_tex_2('#skF_4',A_169)
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169)
      | v1_xboole_0(u1_struct_0(A_169)) ) ),
    inference(resolution,[status(thm)],[c_95,c_2289])).

tff(c_112,plain,(
    ! [A_54,B_55] :
      ( k6_domain_1(A_54,B_55) = k1_tarski(B_55)
      | ~ m1_subset_1(B_55,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_119,plain,(
    ! [A_1] :
      ( k6_domain_1(A_1,'#skF_1'(A_1)) = k1_tarski('#skF_1'(A_1))
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_95,c_112])).

tff(c_2401,plain,(
    ! [A_172] :
      ( k1_tarski('#skF_1'(u1_struct_0(A_172))) = '#skF_4'
      | v1_xboole_0(u1_struct_0(A_172))
      | ~ v3_tex_2('#skF_4',A_172)
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172)
      | v1_xboole_0(u1_struct_0(A_172)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2315,c_119])).

tff(c_12,plain,(
    ! [A_7] : ~ v1_xboole_0(k1_tarski(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2464,plain,(
    ! [A_172] :
      ( ~ v1_xboole_0('#skF_4')
      | v1_xboole_0(u1_struct_0(A_172))
      | ~ v3_tex_2('#skF_4',A_172)
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172)
      | v1_xboole_0(u1_struct_0(A_172)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2401,c_12])).

tff(c_2475,plain,(
    ! [A_173] :
      ( ~ v3_tex_2('#skF_4',A_173)
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173)
      | v1_xboole_0(u1_struct_0(A_173)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2464])).

tff(c_22,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2484,plain,(
    ! [A_174] :
      ( ~ l1_struct_0(A_174)
      | ~ v3_tex_2('#skF_4',A_174)
      | ~ l1_pre_topc(A_174)
      | ~ v2_pre_topc(A_174)
      | v2_struct_0(A_174) ) ),
    inference(resolution,[status(thm)],[c_2475,c_22])).

tff(c_2490,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_2484])).

tff(c_2494,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2490])).

tff(c_2495,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2494])).

tff(c_2498,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_2495])).

tff(c_2502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2498])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.62/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.62/1.90  
% 4.62/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.62/1.90  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 4.62/1.90  
% 4.62/1.90  %Foreground sorts:
% 4.62/1.90  
% 4.62/1.90  
% 4.62/1.90  %Background operators:
% 4.62/1.90  
% 4.62/1.90  
% 4.62/1.90  %Foreground operators:
% 4.62/1.90  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.62/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.62/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.62/1.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.62/1.90  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.62/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.62/1.90  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.62/1.90  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.62/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.62/1.90  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.62/1.90  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.62/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.62/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.62/1.90  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.62/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.62/1.90  tff('#skF_4', type, '#skF_4': $i).
% 4.62/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.62/1.90  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.62/1.90  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.62/1.90  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.62/1.90  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.62/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.62/1.90  
% 5.00/1.92  tff(f_125, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 5.00/1.92  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.00/1.92  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.00/1.92  tff(f_47, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 5.00/1.92  tff(f_109, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 5.00/1.92  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 5.00/1.92  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.00/1.92  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.00/1.92  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.00/1.92  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 5.00/1.92  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.00/1.92  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 5.00/1.92  tff(f_65, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.00/1.92  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.00/1.92  tff(c_20, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.00/1.92  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.00/1.92  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.00/1.92  tff(c_42, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.00/1.92  tff(c_46, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.00/1.92  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.00/1.92  tff(c_91, plain, (![A_45, B_46]: (m1_subset_1(A_45, B_46) | ~r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.00/1.92  tff(c_95, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_91])).
% 5.00/1.92  tff(c_40, plain, (![A_30, B_32]: (v2_tex_2(k6_domain_1(u1_struct_0(A_30), B_32), A_30) | ~m1_subset_1(B_32, u1_struct_0(A_30)) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.00/1.92  tff(c_24, plain, (![A_16, B_17]: (m1_subset_1(k6_domain_1(A_16, B_17), k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.00/1.92  tff(c_57, plain, (![A_38]: (k1_xboole_0=A_38 | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.00/1.92  tff(c_66, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_46, c_57])).
% 5.00/1.92  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.00/1.92  tff(c_68, plain, (![A_8]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_14])).
% 5.00/1.92  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.00/1.92  tff(c_69, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_10])).
% 5.00/1.92  tff(c_549, plain, (![C_95, B_96, A_97]: (C_95=B_96 | ~r1_tarski(B_96, C_95) | ~v2_tex_2(C_95, A_97) | ~m1_subset_1(C_95, k1_zfmisc_1(u1_struct_0(A_97))) | ~v3_tex_2(B_96, A_97) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.00/1.92  tff(c_551, plain, (![A_6, A_97]: (A_6='#skF_4' | ~v2_tex_2(A_6, A_97) | ~m1_subset_1(A_6, k1_zfmisc_1(u1_struct_0(A_97))) | ~v3_tex_2('#skF_4', A_97) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(resolution, [status(thm)], [c_69, c_549])).
% 5.00/1.92  tff(c_754, plain, (![A_105, A_106]: (A_105='#skF_4' | ~v2_tex_2(A_105, A_106) | ~m1_subset_1(A_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~v3_tex_2('#skF_4', A_106) | ~l1_pre_topc(A_106))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_551])).
% 5.00/1.92  tff(c_2268, plain, (![A_165, B_166]: (k6_domain_1(u1_struct_0(A_165), B_166)='#skF_4' | ~v2_tex_2(k6_domain_1(u1_struct_0(A_165), B_166), A_165) | ~v3_tex_2('#skF_4', A_165) | ~l1_pre_topc(A_165) | ~m1_subset_1(B_166, u1_struct_0(A_165)) | v1_xboole_0(u1_struct_0(A_165)))), inference(resolution, [status(thm)], [c_24, c_754])).
% 5.00/1.92  tff(c_2289, plain, (![A_167, B_168]: (k6_domain_1(u1_struct_0(A_167), B_168)='#skF_4' | ~v3_tex_2('#skF_4', A_167) | v1_xboole_0(u1_struct_0(A_167)) | ~m1_subset_1(B_168, u1_struct_0(A_167)) | ~l1_pre_topc(A_167) | ~v2_pre_topc(A_167) | v2_struct_0(A_167))), inference(resolution, [status(thm)], [c_40, c_2268])).
% 5.00/1.92  tff(c_2315, plain, (![A_169]: (k6_domain_1(u1_struct_0(A_169), '#skF_1'(u1_struct_0(A_169)))='#skF_4' | ~v3_tex_2('#skF_4', A_169) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169) | v1_xboole_0(u1_struct_0(A_169)))), inference(resolution, [status(thm)], [c_95, c_2289])).
% 5.00/1.92  tff(c_112, plain, (![A_54, B_55]: (k6_domain_1(A_54, B_55)=k1_tarski(B_55) | ~m1_subset_1(B_55, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.00/1.92  tff(c_119, plain, (![A_1]: (k6_domain_1(A_1, '#skF_1'(A_1))=k1_tarski('#skF_1'(A_1)) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_95, c_112])).
% 5.00/1.92  tff(c_2401, plain, (![A_172]: (k1_tarski('#skF_1'(u1_struct_0(A_172)))='#skF_4' | v1_xboole_0(u1_struct_0(A_172)) | ~v3_tex_2('#skF_4', A_172) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172) | v1_xboole_0(u1_struct_0(A_172)))), inference(superposition, [status(thm), theory('equality')], [c_2315, c_119])).
% 5.00/1.92  tff(c_12, plain, (![A_7]: (~v1_xboole_0(k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.00/1.92  tff(c_2464, plain, (![A_172]: (~v1_xboole_0('#skF_4') | v1_xboole_0(u1_struct_0(A_172)) | ~v3_tex_2('#skF_4', A_172) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172) | v1_xboole_0(u1_struct_0(A_172)))), inference(superposition, [status(thm), theory('equality')], [c_2401, c_12])).
% 5.00/1.92  tff(c_2475, plain, (![A_173]: (~v3_tex_2('#skF_4', A_173) | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173) | v1_xboole_0(u1_struct_0(A_173)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2464])).
% 5.00/1.92  tff(c_22, plain, (![A_15]: (~v1_xboole_0(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.00/1.92  tff(c_2484, plain, (![A_174]: (~l1_struct_0(A_174) | ~v3_tex_2('#skF_4', A_174) | ~l1_pre_topc(A_174) | ~v2_pre_topc(A_174) | v2_struct_0(A_174))), inference(resolution, [status(thm)], [c_2475, c_22])).
% 5.00/1.92  tff(c_2490, plain, (~l1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_2484])).
% 5.00/1.92  tff(c_2494, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2490])).
% 5.00/1.92  tff(c_2495, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_2494])).
% 5.00/1.92  tff(c_2498, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_2495])).
% 5.00/1.92  tff(c_2502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_2498])).
% 5.00/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.00/1.92  
% 5.00/1.92  Inference rules
% 5.00/1.92  ----------------------
% 5.00/1.92  #Ref     : 0
% 5.00/1.92  #Sup     : 544
% 5.00/1.92  #Fact    : 0
% 5.00/1.92  #Define  : 0
% 5.00/1.92  #Split   : 5
% 5.00/1.92  #Chain   : 0
% 5.00/1.92  #Close   : 0
% 5.00/1.92  
% 5.00/1.92  Ordering : KBO
% 5.00/1.92  
% 5.00/1.92  Simplification rules
% 5.00/1.92  ----------------------
% 5.00/1.92  #Subsume      : 56
% 5.00/1.92  #Demod        : 629
% 5.00/1.92  #Tautology    : 221
% 5.00/1.92  #SimpNegUnit  : 153
% 5.00/1.92  #BackRed      : 13
% 5.00/1.92  
% 5.00/1.92  #Partial instantiations: 0
% 5.00/1.92  #Strategies tried      : 1
% 5.00/1.92  
% 5.00/1.92  Timing (in seconds)
% 5.00/1.92  ----------------------
% 5.00/1.92  Preprocessing        : 0.33
% 5.00/1.92  Parsing              : 0.18
% 5.00/1.92  CNF conversion       : 0.02
% 5.00/1.92  Main loop            : 0.80
% 5.00/1.92  Inferencing          : 0.26
% 5.00/1.92  Reduction            : 0.26
% 5.00/1.92  Demodulation         : 0.18
% 5.00/1.92  BG Simplification    : 0.03
% 5.00/1.92  Subsumption          : 0.19
% 5.00/1.92  Abstraction          : 0.04
% 5.00/1.92  MUC search           : 0.00
% 5.00/1.92  Cooper               : 0.00
% 5.00/1.92  Total                : 1.17
% 5.00/1.92  Index Insertion      : 0.00
% 5.00/1.92  Index Deletion       : 0.00
% 5.00/1.92  Index Matching       : 0.00
% 5.00/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
