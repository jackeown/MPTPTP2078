%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:57 EST 2020

% Result     : Theorem 13.50s
% Output     : CNFRefutation 13.63s
% Verified   : 
% Statistics : Number of formulae       :   73 (  90 expanded)
%              Number of leaves         :   36 (  46 expanded)
%              Depth                    :   16
%              Number of atoms          :  161 ( 220 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_119,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_107,axiom,(
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

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_54,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_52,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_46,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_50,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_89,plain,(
    ! [A_47] :
      ( v1_xboole_0(A_47)
      | r2_hidden('#skF_1'(A_47),A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,B_13)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_96,plain,(
    ! [A_47] :
      ( m1_subset_1('#skF_1'(A_47),A_47)
      | v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_89,c_18])).

tff(c_44,plain,(
    ! [A_33,B_35] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_33),B_35),A_33)
      | ~ m1_subset_1(B_35,u1_struct_0(A_33))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k6_domain_1(A_19,B_20),k1_zfmisc_1(A_19))
      | ~ m1_subset_1(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_59,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_68,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_59])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_78,plain,(
    ! [A_8] : m1_subset_1('#skF_5',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_14])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_70,plain,(
    ! [A_6] : r1_tarski('#skF_5',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_10])).

tff(c_636,plain,(
    ! [C_103,B_104,A_105] :
      ( C_103 = B_104
      | ~ r1_tarski(B_104,C_103)
      | ~ v2_tex_2(C_103,A_105)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ v3_tex_2(B_104,A_105)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_638,plain,(
    ! [A_6,A_105] :
      ( A_6 = '#skF_5'
      | ~ v2_tex_2(A_6,A_105)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ v3_tex_2('#skF_5',A_105)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(resolution,[status(thm)],[c_70,c_636])).

tff(c_914,plain,(
    ! [A_116,A_117] :
      ( A_116 = '#skF_5'
      | ~ v2_tex_2(A_116,A_117)
      | ~ m1_subset_1(A_116,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ v3_tex_2('#skF_5',A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_638])).

tff(c_29365,plain,(
    ! [A_426,B_427] :
      ( k6_domain_1(u1_struct_0(A_426),B_427) = '#skF_5'
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_426),B_427),A_426)
      | ~ v3_tex_2('#skF_5',A_426)
      | ~ l1_pre_topc(A_426)
      | ~ m1_subset_1(B_427,u1_struct_0(A_426))
      | v1_xboole_0(u1_struct_0(A_426)) ) ),
    inference(resolution,[status(thm)],[c_28,c_914])).

tff(c_29389,plain,(
    ! [A_428,B_429] :
      ( k6_domain_1(u1_struct_0(A_428),B_429) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_428)
      | v1_xboole_0(u1_struct_0(A_428))
      | ~ m1_subset_1(B_429,u1_struct_0(A_428))
      | ~ l1_pre_topc(A_428)
      | ~ v2_pre_topc(A_428)
      | v2_struct_0(A_428) ) ),
    inference(resolution,[status(thm)],[c_44,c_29365])).

tff(c_29423,plain,(
    ! [A_430] :
      ( k6_domain_1(u1_struct_0(A_430),'#skF_1'(u1_struct_0(A_430))) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_430)
      | ~ l1_pre_topc(A_430)
      | ~ v2_pre_topc(A_430)
      | v2_struct_0(A_430)
      | v1_xboole_0(u1_struct_0(A_430)) ) ),
    inference(resolution,[status(thm)],[c_96,c_29389])).

tff(c_150,plain,(
    ! [A_59,B_60] :
      ( k6_domain_1(A_59,B_60) = k1_tarski(B_60)
      | ~ m1_subset_1(B_60,A_59)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_157,plain,(
    ! [A_47] :
      ( k6_domain_1(A_47,'#skF_1'(A_47)) = k1_tarski('#skF_1'(A_47))
      | v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_96,c_150])).

tff(c_29494,plain,(
    ! [A_431] :
      ( k1_tarski('#skF_1'(u1_struct_0(A_431))) = '#skF_5'
      | v1_xboole_0(u1_struct_0(A_431))
      | ~ v3_tex_2('#skF_5',A_431)
      | ~ l1_pre_topc(A_431)
      | ~ v2_pre_topc(A_431)
      | v2_struct_0(A_431)
      | v1_xboole_0(u1_struct_0(A_431)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29423,c_157])).

tff(c_12,plain,(
    ! [A_7] : ~ v1_xboole_0(k1_tarski(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_29706,plain,(
    ! [A_431] :
      ( ~ v1_xboole_0('#skF_5')
      | v1_xboole_0(u1_struct_0(A_431))
      | ~ v3_tex_2('#skF_5',A_431)
      | ~ l1_pre_topc(A_431)
      | ~ v2_pre_topc(A_431)
      | v2_struct_0(A_431)
      | v1_xboole_0(u1_struct_0(A_431)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29494,c_12])).

tff(c_29721,plain,(
    ! [A_432] :
      ( ~ v3_tex_2('#skF_5',A_432)
      | ~ l1_pre_topc(A_432)
      | ~ v2_pre_topc(A_432)
      | v2_struct_0(A_432)
      | v1_xboole_0(u1_struct_0(A_432)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_29706])).

tff(c_220,plain,(
    ! [A_70] :
      ( m1_subset_1('#skF_2'(A_70),k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    ! [B_11,A_9] :
      ( v1_xboole_0(B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_9))
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_231,plain,(
    ! [A_70] :
      ( v1_xboole_0('#skF_2'(A_70))
      | ~ v1_xboole_0(u1_struct_0(A_70))
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_220,c_16])).

tff(c_29734,plain,(
    ! [A_433] :
      ( v1_xboole_0('#skF_2'(A_433))
      | ~ v3_tex_2('#skF_5',A_433)
      | ~ l1_pre_topc(A_433)
      | ~ v2_pre_topc(A_433)
      | v2_struct_0(A_433) ) ),
    inference(resolution,[status(thm)],[c_29721,c_231])).

tff(c_24,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0('#skF_2'(A_17))
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_29743,plain,(
    ! [A_434] :
      ( ~ v3_tex_2('#skF_5',A_434)
      | ~ l1_pre_topc(A_434)
      | ~ v2_pre_topc(A_434)
      | v2_struct_0(A_434) ) ),
    inference(resolution,[status(thm)],[c_29734,c_24])).

tff(c_29749,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_29743])).

tff(c_29753,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_29749])).

tff(c_29755,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_29753])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.50/6.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.50/6.48  
% 13.50/6.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.50/6.48  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 13.50/6.48  
% 13.50/6.48  %Foreground sorts:
% 13.50/6.48  
% 13.50/6.48  
% 13.50/6.48  %Background operators:
% 13.50/6.48  
% 13.50/6.48  
% 13.50/6.48  %Foreground operators:
% 13.50/6.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 13.50/6.48  tff('#skF_2', type, '#skF_2': $i > $i).
% 13.50/6.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.50/6.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.50/6.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.50/6.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.50/6.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.50/6.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 13.50/6.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 13.50/6.48  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 13.50/6.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.50/6.48  tff('#skF_5', type, '#skF_5': $i).
% 13.50/6.48  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 13.50/6.48  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 13.50/6.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.50/6.48  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 13.50/6.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.50/6.48  tff('#skF_4', type, '#skF_4': $i).
% 13.50/6.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.50/6.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 13.50/6.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.50/6.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.50/6.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.50/6.48  
% 13.63/6.50  tff(f_135, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 13.63/6.50  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 13.63/6.50  tff(f_54, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 13.63/6.50  tff(f_119, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 13.63/6.50  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 13.63/6.50  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 13.63/6.50  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 13.63/6.50  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.63/6.50  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 13.63/6.50  tff(f_89, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 13.63/6.50  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 13.63/6.50  tff(f_75, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 13.63/6.50  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 13.63/6.50  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 13.63/6.50  tff(c_54, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 13.63/6.50  tff(c_52, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 13.63/6.50  tff(c_46, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 13.63/6.50  tff(c_50, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 13.63/6.50  tff(c_89, plain, (![A_47]: (v1_xboole_0(A_47) | r2_hidden('#skF_1'(A_47), A_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.63/6.50  tff(c_18, plain, (![A_12, B_13]: (m1_subset_1(A_12, B_13) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.63/6.50  tff(c_96, plain, (![A_47]: (m1_subset_1('#skF_1'(A_47), A_47) | v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_89, c_18])).
% 13.63/6.50  tff(c_44, plain, (![A_33, B_35]: (v2_tex_2(k6_domain_1(u1_struct_0(A_33), B_35), A_33) | ~m1_subset_1(B_35, u1_struct_0(A_33)) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_119])).
% 13.63/6.50  tff(c_28, plain, (![A_19, B_20]: (m1_subset_1(k6_domain_1(A_19, B_20), k1_zfmisc_1(A_19)) | ~m1_subset_1(B_20, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_82])).
% 13.63/6.50  tff(c_59, plain, (![A_39]: (k1_xboole_0=A_39 | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_36])).
% 13.63/6.50  tff(c_68, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_59])).
% 13.63/6.50  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.63/6.50  tff(c_78, plain, (![A_8]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_14])).
% 13.63/6.50  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.63/6.50  tff(c_70, plain, (![A_6]: (r1_tarski('#skF_5', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_10])).
% 13.63/6.50  tff(c_636, plain, (![C_103, B_104, A_105]: (C_103=B_104 | ~r1_tarski(B_104, C_103) | ~v2_tex_2(C_103, A_105) | ~m1_subset_1(C_103, k1_zfmisc_1(u1_struct_0(A_105))) | ~v3_tex_2(B_104, A_105) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.63/6.50  tff(c_638, plain, (![A_6, A_105]: (A_6='#skF_5' | ~v2_tex_2(A_6, A_105) | ~m1_subset_1(A_6, k1_zfmisc_1(u1_struct_0(A_105))) | ~v3_tex_2('#skF_5', A_105) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(resolution, [status(thm)], [c_70, c_636])).
% 13.63/6.50  tff(c_914, plain, (![A_116, A_117]: (A_116='#skF_5' | ~v2_tex_2(A_116, A_117) | ~m1_subset_1(A_116, k1_zfmisc_1(u1_struct_0(A_117))) | ~v3_tex_2('#skF_5', A_117) | ~l1_pre_topc(A_117))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_638])).
% 13.63/6.50  tff(c_29365, plain, (![A_426, B_427]: (k6_domain_1(u1_struct_0(A_426), B_427)='#skF_5' | ~v2_tex_2(k6_domain_1(u1_struct_0(A_426), B_427), A_426) | ~v3_tex_2('#skF_5', A_426) | ~l1_pre_topc(A_426) | ~m1_subset_1(B_427, u1_struct_0(A_426)) | v1_xboole_0(u1_struct_0(A_426)))), inference(resolution, [status(thm)], [c_28, c_914])).
% 13.63/6.50  tff(c_29389, plain, (![A_428, B_429]: (k6_domain_1(u1_struct_0(A_428), B_429)='#skF_5' | ~v3_tex_2('#skF_5', A_428) | v1_xboole_0(u1_struct_0(A_428)) | ~m1_subset_1(B_429, u1_struct_0(A_428)) | ~l1_pre_topc(A_428) | ~v2_pre_topc(A_428) | v2_struct_0(A_428))), inference(resolution, [status(thm)], [c_44, c_29365])).
% 13.63/6.50  tff(c_29423, plain, (![A_430]: (k6_domain_1(u1_struct_0(A_430), '#skF_1'(u1_struct_0(A_430)))='#skF_5' | ~v3_tex_2('#skF_5', A_430) | ~l1_pre_topc(A_430) | ~v2_pre_topc(A_430) | v2_struct_0(A_430) | v1_xboole_0(u1_struct_0(A_430)))), inference(resolution, [status(thm)], [c_96, c_29389])).
% 13.63/6.50  tff(c_150, plain, (![A_59, B_60]: (k6_domain_1(A_59, B_60)=k1_tarski(B_60) | ~m1_subset_1(B_60, A_59) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.63/6.50  tff(c_157, plain, (![A_47]: (k6_domain_1(A_47, '#skF_1'(A_47))=k1_tarski('#skF_1'(A_47)) | v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_96, c_150])).
% 13.63/6.50  tff(c_29494, plain, (![A_431]: (k1_tarski('#skF_1'(u1_struct_0(A_431)))='#skF_5' | v1_xboole_0(u1_struct_0(A_431)) | ~v3_tex_2('#skF_5', A_431) | ~l1_pre_topc(A_431) | ~v2_pre_topc(A_431) | v2_struct_0(A_431) | v1_xboole_0(u1_struct_0(A_431)))), inference(superposition, [status(thm), theory('equality')], [c_29423, c_157])).
% 13.63/6.50  tff(c_12, plain, (![A_7]: (~v1_xboole_0(k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.63/6.50  tff(c_29706, plain, (![A_431]: (~v1_xboole_0('#skF_5') | v1_xboole_0(u1_struct_0(A_431)) | ~v3_tex_2('#skF_5', A_431) | ~l1_pre_topc(A_431) | ~v2_pre_topc(A_431) | v2_struct_0(A_431) | v1_xboole_0(u1_struct_0(A_431)))), inference(superposition, [status(thm), theory('equality')], [c_29494, c_12])).
% 13.63/6.50  tff(c_29721, plain, (![A_432]: (~v3_tex_2('#skF_5', A_432) | ~l1_pre_topc(A_432) | ~v2_pre_topc(A_432) | v2_struct_0(A_432) | v1_xboole_0(u1_struct_0(A_432)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_29706])).
% 13.63/6.50  tff(c_220, plain, (![A_70]: (m1_subset_1('#skF_2'(A_70), k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.63/6.50  tff(c_16, plain, (![B_11, A_9]: (v1_xboole_0(B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_9)) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.63/6.50  tff(c_231, plain, (![A_70]: (v1_xboole_0('#skF_2'(A_70)) | ~v1_xboole_0(u1_struct_0(A_70)) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(resolution, [status(thm)], [c_220, c_16])).
% 13.63/6.50  tff(c_29734, plain, (![A_433]: (v1_xboole_0('#skF_2'(A_433)) | ~v3_tex_2('#skF_5', A_433) | ~l1_pre_topc(A_433) | ~v2_pre_topc(A_433) | v2_struct_0(A_433))), inference(resolution, [status(thm)], [c_29721, c_231])).
% 13.63/6.50  tff(c_24, plain, (![A_17]: (~v1_xboole_0('#skF_2'(A_17)) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.63/6.50  tff(c_29743, plain, (![A_434]: (~v3_tex_2('#skF_5', A_434) | ~l1_pre_topc(A_434) | ~v2_pre_topc(A_434) | v2_struct_0(A_434))), inference(resolution, [status(thm)], [c_29734, c_24])).
% 13.63/6.50  tff(c_29749, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_29743])).
% 13.63/6.50  tff(c_29753, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_29749])).
% 13.63/6.50  tff(c_29755, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_29753])).
% 13.63/6.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.63/6.50  
% 13.63/6.50  Inference rules
% 13.63/6.50  ----------------------
% 13.63/6.50  #Ref     : 0
% 13.63/6.50  #Sup     : 6901
% 13.63/6.50  #Fact    : 0
% 13.63/6.50  #Define  : 0
% 13.63/6.50  #Split   : 5
% 13.63/6.50  #Chain   : 0
% 13.63/6.50  #Close   : 0
% 13.63/6.50  
% 13.63/6.50  Ordering : KBO
% 13.63/6.50  
% 13.63/6.50  Simplification rules
% 13.63/6.50  ----------------------
% 13.63/6.50  #Subsume      : 1895
% 13.63/6.50  #Demod        : 7715
% 13.63/6.50  #Tautology    : 2507
% 13.63/6.50  #SimpNegUnit  : 2555
% 13.63/6.50  #BackRed      : 10
% 13.63/6.50  
% 13.63/6.50  #Partial instantiations: 0
% 13.63/6.50  #Strategies tried      : 1
% 13.63/6.50  
% 13.63/6.50  Timing (in seconds)
% 13.63/6.50  ----------------------
% 13.63/6.50  Preprocessing        : 0.31
% 13.63/6.50  Parsing              : 0.16
% 13.63/6.50  CNF conversion       : 0.02
% 13.63/6.50  Main loop            : 5.35
% 13.63/6.50  Inferencing          : 1.02
% 13.63/6.50  Reduction            : 1.53
% 13.63/6.50  Demodulation         : 1.05
% 13.63/6.50  BG Simplification    : 0.12
% 13.63/6.50  Subsumption          : 2.46
% 13.63/6.50  Abstraction          : 0.21
% 13.63/6.50  MUC search           : 0.00
% 13.63/6.50  Cooper               : 0.00
% 13.63/6.50  Total                : 5.70
% 13.63/6.50  Index Insertion      : 0.00
% 13.63/6.50  Index Deletion       : 0.00
% 13.63/6.50  Index Matching       : 0.00
% 13.63/6.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
