%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:01 EST 2020

% Result     : Theorem 5.08s
% Output     : CNFRefutation 5.08s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 113 expanded)
%              Number of leaves         :   38 (  54 expanded)
%              Depth                    :   16
%              Number of atoms          :  201 ( 306 expanded)
%              Number of equality atoms :   21 (  30 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_72,axiom,(
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
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_116,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_104,axiom,(
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

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_52,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_50,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_65,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_65])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,(
    ! [A_6] : k2_xboole_0(A_6,'#skF_5') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_8])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),B_9) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_97,plain,(
    ! [A_44,B_45] : k2_xboole_0(k1_tarski(A_44),B_45) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_12])).

tff(c_101,plain,(
    ! [A_44] : k1_tarski(A_44) != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_97])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_162,plain,(
    ! [A_65] :
      ( m1_subset_1('#skF_2'(A_65),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    ! [A_11,C_13,B_12] :
      ( m1_subset_1(A_11,C_13)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(C_13))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_225,plain,(
    ! [A_78,A_79] :
      ( m1_subset_1(A_78,u1_struct_0(A_79))
      | ~ r2_hidden(A_78,'#skF_2'(A_79))
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_162,c_16])).

tff(c_230,plain,(
    ! [A_79] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_79)),u1_struct_0(A_79))
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79)
      | v1_xboole_0('#skF_2'(A_79)) ) ),
    inference(resolution,[status(thm)],[c_4,c_225])).

tff(c_42,plain,(
    ! [A_33,B_35] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_33),B_35),A_33)
      | ~ m1_subset_1(B_35,u1_struct_0(A_33))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k6_domain_1(A_19,B_20),k1_zfmisc_1(A_19))
      | ~ m1_subset_1(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_14,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_78,plain,(
    ! [A_10] : m1_subset_1('#skF_5',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_14])).

tff(c_10,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_72,plain,(
    ! [A_7] : r1_tarski('#skF_5',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_10])).

tff(c_421,plain,(
    ! [C_98,B_99,A_100] :
      ( C_98 = B_99
      | ~ r1_tarski(B_99,C_98)
      | ~ v2_tex_2(C_98,A_100)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ v3_tex_2(B_99,A_100)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_423,plain,(
    ! [A_7,A_100] :
      ( A_7 = '#skF_5'
      | ~ v2_tex_2(A_7,A_100)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ v3_tex_2('#skF_5',A_100)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(resolution,[status(thm)],[c_72,c_421])).

tff(c_427,plain,(
    ! [A_101,A_102] :
      ( A_101 = '#skF_5'
      | ~ v2_tex_2(A_101,A_102)
      | ~ m1_subset_1(A_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ v3_tex_2('#skF_5',A_102)
      | ~ l1_pre_topc(A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_423])).

tff(c_1007,plain,(
    ! [A_150,B_151] :
      ( k6_domain_1(u1_struct_0(A_150),B_151) = '#skF_5'
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_150),B_151),A_150)
      | ~ v3_tex_2('#skF_5',A_150)
      | ~ l1_pre_topc(A_150)
      | ~ m1_subset_1(B_151,u1_struct_0(A_150))
      | v1_xboole_0(u1_struct_0(A_150)) ) ),
    inference(resolution,[status(thm)],[c_26,c_427])).

tff(c_1027,plain,(
    ! [A_154,B_155] :
      ( k6_domain_1(u1_struct_0(A_154),B_155) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_154)
      | v1_xboole_0(u1_struct_0(A_154))
      | ~ m1_subset_1(B_155,u1_struct_0(A_154))
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(resolution,[status(thm)],[c_42,c_1007])).

tff(c_1037,plain,(
    ! [A_156] :
      ( k6_domain_1(u1_struct_0(A_156),'#skF_1'('#skF_2'(A_156))) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_156)
      | v1_xboole_0(u1_struct_0(A_156))
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156)
      | v1_xboole_0('#skF_2'(A_156)) ) ),
    inference(resolution,[status(thm)],[c_230,c_1027])).

tff(c_257,plain,(
    ! [A_86] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_86)),u1_struct_0(A_86))
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86)
      | v2_struct_0(A_86)
      | v1_xboole_0('#skF_2'(A_86)) ) ),
    inference(resolution,[status(thm)],[c_4,c_225])).

tff(c_28,plain,(
    ! [A_21,B_22] :
      ( k6_domain_1(A_21,B_22) = k1_tarski(B_22)
      | ~ m1_subset_1(B_22,A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_261,plain,(
    ! [A_86] :
      ( k6_domain_1(u1_struct_0(A_86),'#skF_1'('#skF_2'(A_86))) = k1_tarski('#skF_1'('#skF_2'(A_86)))
      | v1_xboole_0(u1_struct_0(A_86))
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86)
      | v2_struct_0(A_86)
      | v1_xboole_0('#skF_2'(A_86)) ) ),
    inference(resolution,[status(thm)],[c_257,c_28])).

tff(c_1049,plain,(
    ! [A_156] :
      ( k1_tarski('#skF_1'('#skF_2'(A_156))) = '#skF_5'
      | v1_xboole_0(u1_struct_0(A_156))
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156)
      | v1_xboole_0('#skF_2'(A_156))
      | ~ v3_tex_2('#skF_5',A_156)
      | v1_xboole_0(u1_struct_0(A_156))
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156)
      | v1_xboole_0('#skF_2'(A_156)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1037,c_261])).

tff(c_1078,plain,(
    ! [A_156] :
      ( v1_xboole_0(u1_struct_0(A_156))
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156)
      | v1_xboole_0('#skF_2'(A_156))
      | ~ v3_tex_2('#skF_5',A_156)
      | v1_xboole_0(u1_struct_0(A_156))
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156)
      | v1_xboole_0('#skF_2'(A_156)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_1049])).

tff(c_1965,plain,(
    ! [A_202] :
      ( ~ v3_tex_2('#skF_5',A_202)
      | ~ l1_pre_topc(A_202)
      | ~ v2_pre_topc(A_202)
      | v2_struct_0(A_202)
      | v1_xboole_0('#skF_2'(A_202))
      | v1_xboole_0(u1_struct_0(A_202)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1078])).

tff(c_18,plain,(
    ! [C_16,B_15,A_14] :
      ( ~ v1_xboole_0(C_16)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(C_16))
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_217,plain,(
    ! [A_73,A_74] :
      ( ~ v1_xboole_0(u1_struct_0(A_73))
      | ~ r2_hidden(A_74,'#skF_2'(A_73))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_162,c_18])).

tff(c_222,plain,(
    ! [A_73] :
      ( ~ v1_xboole_0(u1_struct_0(A_73))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73)
      | v1_xboole_0('#skF_2'(A_73)) ) ),
    inference(resolution,[status(thm)],[c_4,c_217])).

tff(c_1979,plain,(
    ! [A_203] :
      ( ~ v3_tex_2('#skF_5',A_203)
      | ~ l1_pre_topc(A_203)
      | ~ v2_pre_topc(A_203)
      | v2_struct_0(A_203)
      | v1_xboole_0('#skF_2'(A_203)) ) ),
    inference(resolution,[status(thm)],[c_1965,c_222])).

tff(c_22,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0('#skF_2'(A_17))
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1988,plain,(
    ! [A_204] :
      ( ~ v3_tex_2('#skF_5',A_204)
      | ~ l1_pre_topc(A_204)
      | ~ v2_pre_topc(A_204)
      | v2_struct_0(A_204) ) ),
    inference(resolution,[status(thm)],[c_1979,c_22])).

tff(c_1994,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1988])).

tff(c_1998,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1994])).

tff(c_2000,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1998])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:39:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.08/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.08/1.95  
% 5.08/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.08/1.95  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 5.08/1.95  
% 5.08/1.95  %Foreground sorts:
% 5.08/1.95  
% 5.08/1.95  
% 5.08/1.95  %Background operators:
% 5.08/1.95  
% 5.08/1.95  
% 5.08/1.95  %Foreground operators:
% 5.08/1.95  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.08/1.95  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.08/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.08/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.08/1.95  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.08/1.95  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.08/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.08/1.95  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.08/1.95  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.08/1.95  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.08/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.08/1.95  tff('#skF_5', type, '#skF_5': $i).
% 5.08/1.95  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 5.08/1.95  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.08/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.08/1.95  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.08/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.08/1.95  tff('#skF_4', type, '#skF_4': $i).
% 5.08/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.08/1.95  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.08/1.95  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.08/1.95  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.08/1.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.08/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.08/1.95  
% 5.08/1.97  tff(f_132, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 5.08/1.97  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.08/1.97  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.08/1.97  tff(f_42, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 5.08/1.97  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.08/1.97  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 5.08/1.97  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 5.08/1.97  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 5.08/1.97  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 5.08/1.97  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.08/1.97  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.08/1.97  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 5.08/1.97  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.08/1.97  tff(f_57, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.08/1.97  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.08/1.97  tff(c_52, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.08/1.97  tff(c_50, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.08/1.97  tff(c_44, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.08/1.97  tff(c_48, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.08/1.97  tff(c_65, plain, (![A_39]: (k1_xboole_0=A_39 | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.08/1.97  tff(c_69, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_48, c_65])).
% 5.08/1.97  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.08/1.97  tff(c_71, plain, (![A_6]: (k2_xboole_0(A_6, '#skF_5')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_69, c_8])).
% 5.08/1.97  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.08/1.97  tff(c_97, plain, (![A_44, B_45]: (k2_xboole_0(k1_tarski(A_44), B_45)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_12])).
% 5.08/1.97  tff(c_101, plain, (![A_44]: (k1_tarski(A_44)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_71, c_97])).
% 5.08/1.97  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.08/1.97  tff(c_162, plain, (![A_65]: (m1_subset_1('#skF_2'(A_65), k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.08/1.97  tff(c_16, plain, (![A_11, C_13, B_12]: (m1_subset_1(A_11, C_13) | ~m1_subset_1(B_12, k1_zfmisc_1(C_13)) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.08/1.97  tff(c_225, plain, (![A_78, A_79]: (m1_subset_1(A_78, u1_struct_0(A_79)) | ~r2_hidden(A_78, '#skF_2'(A_79)) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79) | v2_struct_0(A_79))), inference(resolution, [status(thm)], [c_162, c_16])).
% 5.08/1.97  tff(c_230, plain, (![A_79]: (m1_subset_1('#skF_1'('#skF_2'(A_79)), u1_struct_0(A_79)) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79) | v2_struct_0(A_79) | v1_xboole_0('#skF_2'(A_79)))), inference(resolution, [status(thm)], [c_4, c_225])).
% 5.08/1.97  tff(c_42, plain, (![A_33, B_35]: (v2_tex_2(k6_domain_1(u1_struct_0(A_33), B_35), A_33) | ~m1_subset_1(B_35, u1_struct_0(A_33)) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.08/1.97  tff(c_26, plain, (![A_19, B_20]: (m1_subset_1(k6_domain_1(A_19, B_20), k1_zfmisc_1(A_19)) | ~m1_subset_1(B_20, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.08/1.97  tff(c_14, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.08/1.97  tff(c_78, plain, (![A_10]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_14])).
% 5.08/1.97  tff(c_10, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.08/1.97  tff(c_72, plain, (![A_7]: (r1_tarski('#skF_5', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_10])).
% 5.08/1.97  tff(c_421, plain, (![C_98, B_99, A_100]: (C_98=B_99 | ~r1_tarski(B_99, C_98) | ~v2_tex_2(C_98, A_100) | ~m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0(A_100))) | ~v3_tex_2(B_99, A_100) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.08/1.97  tff(c_423, plain, (![A_7, A_100]: (A_7='#skF_5' | ~v2_tex_2(A_7, A_100) | ~m1_subset_1(A_7, k1_zfmisc_1(u1_struct_0(A_100))) | ~v3_tex_2('#skF_5', A_100) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(resolution, [status(thm)], [c_72, c_421])).
% 5.08/1.97  tff(c_427, plain, (![A_101, A_102]: (A_101='#skF_5' | ~v2_tex_2(A_101, A_102) | ~m1_subset_1(A_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~v3_tex_2('#skF_5', A_102) | ~l1_pre_topc(A_102))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_423])).
% 5.08/1.97  tff(c_1007, plain, (![A_150, B_151]: (k6_domain_1(u1_struct_0(A_150), B_151)='#skF_5' | ~v2_tex_2(k6_domain_1(u1_struct_0(A_150), B_151), A_150) | ~v3_tex_2('#skF_5', A_150) | ~l1_pre_topc(A_150) | ~m1_subset_1(B_151, u1_struct_0(A_150)) | v1_xboole_0(u1_struct_0(A_150)))), inference(resolution, [status(thm)], [c_26, c_427])).
% 5.08/1.97  tff(c_1027, plain, (![A_154, B_155]: (k6_domain_1(u1_struct_0(A_154), B_155)='#skF_5' | ~v3_tex_2('#skF_5', A_154) | v1_xboole_0(u1_struct_0(A_154)) | ~m1_subset_1(B_155, u1_struct_0(A_154)) | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(resolution, [status(thm)], [c_42, c_1007])).
% 5.08/1.97  tff(c_1037, plain, (![A_156]: (k6_domain_1(u1_struct_0(A_156), '#skF_1'('#skF_2'(A_156)))='#skF_5' | ~v3_tex_2('#skF_5', A_156) | v1_xboole_0(u1_struct_0(A_156)) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156) | v1_xboole_0('#skF_2'(A_156)))), inference(resolution, [status(thm)], [c_230, c_1027])).
% 5.08/1.97  tff(c_257, plain, (![A_86]: (m1_subset_1('#skF_1'('#skF_2'(A_86)), u1_struct_0(A_86)) | ~l1_pre_topc(A_86) | ~v2_pre_topc(A_86) | v2_struct_0(A_86) | v1_xboole_0('#skF_2'(A_86)))), inference(resolution, [status(thm)], [c_4, c_225])).
% 5.08/1.97  tff(c_28, plain, (![A_21, B_22]: (k6_domain_1(A_21, B_22)=k1_tarski(B_22) | ~m1_subset_1(B_22, A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.08/1.97  tff(c_261, plain, (![A_86]: (k6_domain_1(u1_struct_0(A_86), '#skF_1'('#skF_2'(A_86)))=k1_tarski('#skF_1'('#skF_2'(A_86))) | v1_xboole_0(u1_struct_0(A_86)) | ~l1_pre_topc(A_86) | ~v2_pre_topc(A_86) | v2_struct_0(A_86) | v1_xboole_0('#skF_2'(A_86)))), inference(resolution, [status(thm)], [c_257, c_28])).
% 5.08/1.97  tff(c_1049, plain, (![A_156]: (k1_tarski('#skF_1'('#skF_2'(A_156)))='#skF_5' | v1_xboole_0(u1_struct_0(A_156)) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156) | v1_xboole_0('#skF_2'(A_156)) | ~v3_tex_2('#skF_5', A_156) | v1_xboole_0(u1_struct_0(A_156)) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156) | v1_xboole_0('#skF_2'(A_156)))), inference(superposition, [status(thm), theory('equality')], [c_1037, c_261])).
% 5.08/1.97  tff(c_1078, plain, (![A_156]: (v1_xboole_0(u1_struct_0(A_156)) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156) | v1_xboole_0('#skF_2'(A_156)) | ~v3_tex_2('#skF_5', A_156) | v1_xboole_0(u1_struct_0(A_156)) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156) | v1_xboole_0('#skF_2'(A_156)))), inference(negUnitSimplification, [status(thm)], [c_101, c_1049])).
% 5.08/1.97  tff(c_1965, plain, (![A_202]: (~v3_tex_2('#skF_5', A_202) | ~l1_pre_topc(A_202) | ~v2_pre_topc(A_202) | v2_struct_0(A_202) | v1_xboole_0('#skF_2'(A_202)) | v1_xboole_0(u1_struct_0(A_202)))), inference(factorization, [status(thm), theory('equality')], [c_1078])).
% 5.08/1.97  tff(c_18, plain, (![C_16, B_15, A_14]: (~v1_xboole_0(C_16) | ~m1_subset_1(B_15, k1_zfmisc_1(C_16)) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.08/1.97  tff(c_217, plain, (![A_73, A_74]: (~v1_xboole_0(u1_struct_0(A_73)) | ~r2_hidden(A_74, '#skF_2'(A_73)) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(resolution, [status(thm)], [c_162, c_18])).
% 5.08/1.97  tff(c_222, plain, (![A_73]: (~v1_xboole_0(u1_struct_0(A_73)) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73) | v1_xboole_0('#skF_2'(A_73)))), inference(resolution, [status(thm)], [c_4, c_217])).
% 5.08/1.97  tff(c_1979, plain, (![A_203]: (~v3_tex_2('#skF_5', A_203) | ~l1_pre_topc(A_203) | ~v2_pre_topc(A_203) | v2_struct_0(A_203) | v1_xboole_0('#skF_2'(A_203)))), inference(resolution, [status(thm)], [c_1965, c_222])).
% 5.08/1.97  tff(c_22, plain, (![A_17]: (~v1_xboole_0('#skF_2'(A_17)) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.08/1.97  tff(c_1988, plain, (![A_204]: (~v3_tex_2('#skF_5', A_204) | ~l1_pre_topc(A_204) | ~v2_pre_topc(A_204) | v2_struct_0(A_204))), inference(resolution, [status(thm)], [c_1979, c_22])).
% 5.08/1.97  tff(c_1994, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_1988])).
% 5.08/1.97  tff(c_1998, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1994])).
% 5.08/1.97  tff(c_2000, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1998])).
% 5.08/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.08/1.97  
% 5.08/1.97  Inference rules
% 5.08/1.97  ----------------------
% 5.08/1.97  #Ref     : 0
% 5.08/1.97  #Sup     : 480
% 5.08/1.97  #Fact    : 2
% 5.08/1.97  #Define  : 0
% 5.08/1.97  #Split   : 5
% 5.08/1.97  #Chain   : 0
% 5.08/1.97  #Close   : 0
% 5.08/1.97  
% 5.08/1.97  Ordering : KBO
% 5.08/1.97  
% 5.08/1.97  Simplification rules
% 5.08/1.97  ----------------------
% 5.08/1.97  #Subsume      : 81
% 5.08/1.97  #Demod        : 130
% 5.08/1.97  #Tautology    : 123
% 5.08/1.97  #SimpNegUnit  : 11
% 5.08/1.97  #BackRed      : 10
% 5.08/1.97  
% 5.08/1.97  #Partial instantiations: 0
% 5.08/1.97  #Strategies tried      : 1
% 5.08/1.97  
% 5.08/1.97  Timing (in seconds)
% 5.08/1.97  ----------------------
% 5.08/1.97  Preprocessing        : 0.34
% 5.08/1.97  Parsing              : 0.18
% 5.08/1.97  CNF conversion       : 0.02
% 5.08/1.97  Main loop            : 0.81
% 5.08/1.98  Inferencing          : 0.29
% 5.08/1.98  Reduction            : 0.24
% 5.08/1.98  Demodulation         : 0.16
% 5.08/1.98  BG Simplification    : 0.04
% 5.08/1.98  Subsumption          : 0.19
% 5.08/1.98  Abstraction          : 0.04
% 5.08/1.98  MUC search           : 0.00
% 5.08/1.98  Cooper               : 0.00
% 5.08/1.98  Total                : 1.18
% 5.08/1.98  Index Insertion      : 0.00
% 5.08/1.98  Index Deletion       : 0.00
% 5.08/1.98  Index Matching       : 0.00
% 5.08/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
