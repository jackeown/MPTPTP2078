%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:57 EST 2020

% Result     : Theorem 8.71s
% Output     : CNFRefutation 8.71s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 108 expanded)
%              Number of leaves         :   36 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :  197 ( 323 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :   11 (   5 average)
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

tff(f_131,negated_conjecture,(
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

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_78,axiom,(
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

tff(f_103,axiom,(
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

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_52,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_50,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_44,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_48,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_145,plain,(
    ! [A_59] :
      ( m1_subset_1('#skF_2'(A_59),k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18,plain,(
    ! [A_12,C_14,B_13] :
      ( m1_subset_1(A_12,C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_205,plain,(
    ! [A_70,A_71] :
      ( m1_subset_1(A_70,u1_struct_0(A_71))
      | ~ r2_hidden(A_70,'#skF_2'(A_71))
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_145,c_18])).

tff(c_210,plain,(
    ! [A_71] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_71)),u1_struct_0(A_71))
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71)
      | v1_xboole_0('#skF_2'(A_71)) ) ),
    inference(resolution,[status(thm)],[c_4,c_205])).

tff(c_317,plain,(
    ! [A_84] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_84)),u1_struct_0(A_84))
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84)
      | v1_xboole_0('#skF_2'(A_84)) ) ),
    inference(resolution,[status(thm)],[c_4,c_205])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( k6_domain_1(A_19,B_20) = k1_tarski(B_20)
      | ~ m1_subset_1(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_834,plain,(
    ! [A_125] :
      ( k6_domain_1(u1_struct_0(A_125),'#skF_1'('#skF_2'(A_125))) = k1_tarski('#skF_1'('#skF_2'(A_125)))
      | v1_xboole_0(u1_struct_0(A_125))
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125)
      | v2_struct_0(A_125)
      | v1_xboole_0('#skF_2'(A_125)) ) ),
    inference(resolution,[status(thm)],[c_317,c_28])).

tff(c_42,plain,(
    ! [A_31,B_33] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_31),B_33),A_31)
      | ~ m1_subset_1(B_33,u1_struct_0(A_31))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_855,plain,(
    ! [A_125] :
      ( v2_tex_2(k1_tarski('#skF_1'('#skF_2'(A_125))),A_125)
      | ~ m1_subset_1('#skF_1'('#skF_2'(A_125)),u1_struct_0(A_125))
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125)
      | v2_struct_0(A_125)
      | v1_xboole_0(u1_struct_0(A_125))
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125)
      | v2_struct_0(A_125)
      | v1_xboole_0('#skF_2'(A_125)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_834,c_42])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k6_domain_1(A_17,B_18),k1_zfmisc_1(A_17))
      | ~ m1_subset_1(B_18,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2881,plain,(
    ! [A_224] :
      ( m1_subset_1(k1_tarski('#skF_1'('#skF_2'(A_224))),k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ m1_subset_1('#skF_1'('#skF_2'(A_224)),u1_struct_0(A_224))
      | v1_xboole_0(u1_struct_0(A_224))
      | v1_xboole_0(u1_struct_0(A_224))
      | ~ l1_pre_topc(A_224)
      | ~ v2_pre_topc(A_224)
      | v2_struct_0(A_224)
      | v1_xboole_0('#skF_2'(A_224)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_834,c_26])).

tff(c_57,plain,(
    ! [A_37] :
      ( k1_xboole_0 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_57])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_76,plain,(
    ! [A_8] : m1_subset_1('#skF_5',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_14])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,(
    ! [A_6] : r1_tarski('#skF_5',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_10])).

tff(c_457,plain,(
    ! [C_93,B_94,A_95] :
      ( C_93 = B_94
      | ~ r1_tarski(B_94,C_93)
      | ~ v2_tex_2(C_93,A_95)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ v3_tex_2(B_94,A_95)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_459,plain,(
    ! [A_6,A_95] :
      ( A_6 = '#skF_5'
      | ~ v2_tex_2(A_6,A_95)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ v3_tex_2('#skF_5',A_95)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(resolution,[status(thm)],[c_68,c_457])).

tff(c_462,plain,(
    ! [A_6,A_95] :
      ( A_6 = '#skF_5'
      | ~ v2_tex_2(A_6,A_95)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ v3_tex_2('#skF_5',A_95)
      | ~ l1_pre_topc(A_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_459])).

tff(c_5496,plain,(
    ! [A_296] :
      ( k1_tarski('#skF_1'('#skF_2'(A_296))) = '#skF_5'
      | ~ v2_tex_2(k1_tarski('#skF_1'('#skF_2'(A_296))),A_296)
      | ~ v3_tex_2('#skF_5',A_296)
      | ~ m1_subset_1('#skF_1'('#skF_2'(A_296)),u1_struct_0(A_296))
      | v1_xboole_0(u1_struct_0(A_296))
      | ~ l1_pre_topc(A_296)
      | ~ v2_pre_topc(A_296)
      | v2_struct_0(A_296)
      | v1_xboole_0('#skF_2'(A_296)) ) ),
    inference(resolution,[status(thm)],[c_2881,c_462])).

tff(c_5501,plain,(
    ! [A_297] :
      ( k1_tarski('#skF_1'('#skF_2'(A_297))) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_297)
      | ~ m1_subset_1('#skF_1'('#skF_2'(A_297)),u1_struct_0(A_297))
      | v1_xboole_0(u1_struct_0(A_297))
      | ~ l1_pre_topc(A_297)
      | ~ v2_pre_topc(A_297)
      | v2_struct_0(A_297)
      | v1_xboole_0('#skF_2'(A_297)) ) ),
    inference(resolution,[status(thm)],[c_855,c_5496])).

tff(c_5699,plain,(
    ! [A_300] :
      ( k1_tarski('#skF_1'('#skF_2'(A_300))) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_300)
      | v1_xboole_0(u1_struct_0(A_300))
      | ~ l1_pre_topc(A_300)
      | ~ v2_pre_topc(A_300)
      | v2_struct_0(A_300)
      | v1_xboole_0('#skF_2'(A_300)) ) ),
    inference(resolution,[status(thm)],[c_210,c_5501])).

tff(c_12,plain,(
    ! [A_7] : ~ v1_xboole_0(k1_tarski(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5721,plain,(
    ! [A_300] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ v3_tex_2('#skF_5',A_300)
      | v1_xboole_0(u1_struct_0(A_300))
      | ~ l1_pre_topc(A_300)
      | ~ v2_pre_topc(A_300)
      | v2_struct_0(A_300)
      | v1_xboole_0('#skF_2'(A_300)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5699,c_12])).

tff(c_5732,plain,(
    ! [A_301] :
      ( ~ v3_tex_2('#skF_5',A_301)
      | v1_xboole_0(u1_struct_0(A_301))
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301)
      | v2_struct_0(A_301)
      | v1_xboole_0('#skF_2'(A_301)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_5721])).

tff(c_16,plain,(
    ! [B_11,A_9] :
      ( v1_xboole_0(B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_9))
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_156,plain,(
    ! [A_59] :
      ( v1_xboole_0('#skF_2'(A_59))
      | ~ v1_xboole_0(u1_struct_0(A_59))
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_145,c_16])).

tff(c_5745,plain,(
    ! [A_302] :
      ( ~ v3_tex_2('#skF_5',A_302)
      | ~ l1_pre_topc(A_302)
      | ~ v2_pre_topc(A_302)
      | v2_struct_0(A_302)
      | v1_xboole_0('#skF_2'(A_302)) ) ),
    inference(resolution,[status(thm)],[c_5732,c_156])).

tff(c_22,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0('#skF_2'(A_15))
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5754,plain,(
    ! [A_303] :
      ( ~ v3_tex_2('#skF_5',A_303)
      | ~ l1_pre_topc(A_303)
      | ~ v2_pre_topc(A_303)
      | v2_struct_0(A_303) ) ),
    inference(resolution,[status(thm)],[c_5745,c_22])).

tff(c_5760,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_5754])).

tff(c_5764,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_5760])).

tff(c_5766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5764])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.71/2.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.71/2.86  
% 8.71/2.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.71/2.87  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 8.71/2.87  
% 8.71/2.87  %Foreground sorts:
% 8.71/2.87  
% 8.71/2.87  
% 8.71/2.87  %Background operators:
% 8.71/2.87  
% 8.71/2.87  
% 8.71/2.87  %Foreground operators:
% 8.71/2.87  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.71/2.87  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.71/2.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.71/2.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.71/2.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.71/2.87  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.71/2.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.71/2.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.71/2.87  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.71/2.87  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 8.71/2.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.71/2.87  tff('#skF_5', type, '#skF_5': $i).
% 8.71/2.87  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 8.71/2.87  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 8.71/2.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.71/2.87  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.71/2.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.71/2.87  tff('#skF_4', type, '#skF_4': $i).
% 8.71/2.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.71/2.87  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.71/2.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.71/2.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.71/2.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.71/2.87  
% 8.71/2.88  tff(f_131, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 8.71/2.88  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.71/2.88  tff(f_71, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 8.71/2.88  tff(f_56, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 8.71/2.88  tff(f_85, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 8.71/2.88  tff(f_115, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 8.71/2.88  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 8.71/2.88  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.71/2.88  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 8.71/2.88  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.71/2.88  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 8.71/2.88  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 8.71/2.88  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 8.71/2.88  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.71/2.88  tff(c_52, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.71/2.88  tff(c_50, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.71/2.88  tff(c_44, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.71/2.88  tff(c_48, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.71/2.88  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.71/2.88  tff(c_145, plain, (![A_59]: (m1_subset_1('#skF_2'(A_59), k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.71/2.88  tff(c_18, plain, (![A_12, C_14, B_13]: (m1_subset_1(A_12, C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.71/2.88  tff(c_205, plain, (![A_70, A_71]: (m1_subset_1(A_70, u1_struct_0(A_71)) | ~r2_hidden(A_70, '#skF_2'(A_71)) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(resolution, [status(thm)], [c_145, c_18])).
% 8.71/2.88  tff(c_210, plain, (![A_71]: (m1_subset_1('#skF_1'('#skF_2'(A_71)), u1_struct_0(A_71)) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71) | v1_xboole_0('#skF_2'(A_71)))), inference(resolution, [status(thm)], [c_4, c_205])).
% 8.71/2.88  tff(c_317, plain, (![A_84]: (m1_subset_1('#skF_1'('#skF_2'(A_84)), u1_struct_0(A_84)) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84) | v1_xboole_0('#skF_2'(A_84)))), inference(resolution, [status(thm)], [c_4, c_205])).
% 8.71/2.88  tff(c_28, plain, (![A_19, B_20]: (k6_domain_1(A_19, B_20)=k1_tarski(B_20) | ~m1_subset_1(B_20, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.71/2.88  tff(c_834, plain, (![A_125]: (k6_domain_1(u1_struct_0(A_125), '#skF_1'('#skF_2'(A_125)))=k1_tarski('#skF_1'('#skF_2'(A_125))) | v1_xboole_0(u1_struct_0(A_125)) | ~l1_pre_topc(A_125) | ~v2_pre_topc(A_125) | v2_struct_0(A_125) | v1_xboole_0('#skF_2'(A_125)))), inference(resolution, [status(thm)], [c_317, c_28])).
% 8.71/2.88  tff(c_42, plain, (![A_31, B_33]: (v2_tex_2(k6_domain_1(u1_struct_0(A_31), B_33), A_31) | ~m1_subset_1(B_33, u1_struct_0(A_31)) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.71/2.88  tff(c_855, plain, (![A_125]: (v2_tex_2(k1_tarski('#skF_1'('#skF_2'(A_125))), A_125) | ~m1_subset_1('#skF_1'('#skF_2'(A_125)), u1_struct_0(A_125)) | ~l1_pre_topc(A_125) | ~v2_pre_topc(A_125) | v2_struct_0(A_125) | v1_xboole_0(u1_struct_0(A_125)) | ~l1_pre_topc(A_125) | ~v2_pre_topc(A_125) | v2_struct_0(A_125) | v1_xboole_0('#skF_2'(A_125)))), inference(superposition, [status(thm), theory('equality')], [c_834, c_42])).
% 8.71/2.88  tff(c_26, plain, (![A_17, B_18]: (m1_subset_1(k6_domain_1(A_17, B_18), k1_zfmisc_1(A_17)) | ~m1_subset_1(B_18, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.71/2.88  tff(c_2881, plain, (![A_224]: (m1_subset_1(k1_tarski('#skF_1'('#skF_2'(A_224))), k1_zfmisc_1(u1_struct_0(A_224))) | ~m1_subset_1('#skF_1'('#skF_2'(A_224)), u1_struct_0(A_224)) | v1_xboole_0(u1_struct_0(A_224)) | v1_xboole_0(u1_struct_0(A_224)) | ~l1_pre_topc(A_224) | ~v2_pre_topc(A_224) | v2_struct_0(A_224) | v1_xboole_0('#skF_2'(A_224)))), inference(superposition, [status(thm), theory('equality')], [c_834, c_26])).
% 8.71/2.88  tff(c_57, plain, (![A_37]: (k1_xboole_0=A_37 | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.71/2.88  tff(c_66, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_48, c_57])).
% 8.71/2.88  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.71/2.88  tff(c_76, plain, (![A_8]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_14])).
% 8.71/2.88  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.71/2.88  tff(c_68, plain, (![A_6]: (r1_tarski('#skF_5', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_10])).
% 8.71/2.88  tff(c_457, plain, (![C_93, B_94, A_95]: (C_93=B_94 | ~r1_tarski(B_94, C_93) | ~v2_tex_2(C_93, A_95) | ~m1_subset_1(C_93, k1_zfmisc_1(u1_struct_0(A_95))) | ~v3_tex_2(B_94, A_95) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.71/2.88  tff(c_459, plain, (![A_6, A_95]: (A_6='#skF_5' | ~v2_tex_2(A_6, A_95) | ~m1_subset_1(A_6, k1_zfmisc_1(u1_struct_0(A_95))) | ~v3_tex_2('#skF_5', A_95) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(resolution, [status(thm)], [c_68, c_457])).
% 8.71/2.88  tff(c_462, plain, (![A_6, A_95]: (A_6='#skF_5' | ~v2_tex_2(A_6, A_95) | ~m1_subset_1(A_6, k1_zfmisc_1(u1_struct_0(A_95))) | ~v3_tex_2('#skF_5', A_95) | ~l1_pre_topc(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_459])).
% 8.71/2.88  tff(c_5496, plain, (![A_296]: (k1_tarski('#skF_1'('#skF_2'(A_296)))='#skF_5' | ~v2_tex_2(k1_tarski('#skF_1'('#skF_2'(A_296))), A_296) | ~v3_tex_2('#skF_5', A_296) | ~m1_subset_1('#skF_1'('#skF_2'(A_296)), u1_struct_0(A_296)) | v1_xboole_0(u1_struct_0(A_296)) | ~l1_pre_topc(A_296) | ~v2_pre_topc(A_296) | v2_struct_0(A_296) | v1_xboole_0('#skF_2'(A_296)))), inference(resolution, [status(thm)], [c_2881, c_462])).
% 8.71/2.88  tff(c_5501, plain, (![A_297]: (k1_tarski('#skF_1'('#skF_2'(A_297)))='#skF_5' | ~v3_tex_2('#skF_5', A_297) | ~m1_subset_1('#skF_1'('#skF_2'(A_297)), u1_struct_0(A_297)) | v1_xboole_0(u1_struct_0(A_297)) | ~l1_pre_topc(A_297) | ~v2_pre_topc(A_297) | v2_struct_0(A_297) | v1_xboole_0('#skF_2'(A_297)))), inference(resolution, [status(thm)], [c_855, c_5496])).
% 8.71/2.88  tff(c_5699, plain, (![A_300]: (k1_tarski('#skF_1'('#skF_2'(A_300)))='#skF_5' | ~v3_tex_2('#skF_5', A_300) | v1_xboole_0(u1_struct_0(A_300)) | ~l1_pre_topc(A_300) | ~v2_pre_topc(A_300) | v2_struct_0(A_300) | v1_xboole_0('#skF_2'(A_300)))), inference(resolution, [status(thm)], [c_210, c_5501])).
% 8.71/2.88  tff(c_12, plain, (![A_7]: (~v1_xboole_0(k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.71/2.88  tff(c_5721, plain, (![A_300]: (~v1_xboole_0('#skF_5') | ~v3_tex_2('#skF_5', A_300) | v1_xboole_0(u1_struct_0(A_300)) | ~l1_pre_topc(A_300) | ~v2_pre_topc(A_300) | v2_struct_0(A_300) | v1_xboole_0('#skF_2'(A_300)))), inference(superposition, [status(thm), theory('equality')], [c_5699, c_12])).
% 8.71/2.88  tff(c_5732, plain, (![A_301]: (~v3_tex_2('#skF_5', A_301) | v1_xboole_0(u1_struct_0(A_301)) | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301) | v2_struct_0(A_301) | v1_xboole_0('#skF_2'(A_301)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_5721])).
% 8.71/2.88  tff(c_16, plain, (![B_11, A_9]: (v1_xboole_0(B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_9)) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.71/2.88  tff(c_156, plain, (![A_59]: (v1_xboole_0('#skF_2'(A_59)) | ~v1_xboole_0(u1_struct_0(A_59)) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(resolution, [status(thm)], [c_145, c_16])).
% 8.71/2.88  tff(c_5745, plain, (![A_302]: (~v3_tex_2('#skF_5', A_302) | ~l1_pre_topc(A_302) | ~v2_pre_topc(A_302) | v2_struct_0(A_302) | v1_xboole_0('#skF_2'(A_302)))), inference(resolution, [status(thm)], [c_5732, c_156])).
% 8.71/2.88  tff(c_22, plain, (![A_15]: (~v1_xboole_0('#skF_2'(A_15)) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.71/2.88  tff(c_5754, plain, (![A_303]: (~v3_tex_2('#skF_5', A_303) | ~l1_pre_topc(A_303) | ~v2_pre_topc(A_303) | v2_struct_0(A_303))), inference(resolution, [status(thm)], [c_5745, c_22])).
% 8.71/2.88  tff(c_5760, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_5754])).
% 8.71/2.88  tff(c_5764, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_5760])).
% 8.71/2.88  tff(c_5766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_5764])).
% 8.71/2.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.71/2.88  
% 8.71/2.88  Inference rules
% 8.71/2.88  ----------------------
% 8.71/2.88  #Ref     : 0
% 8.71/2.88  #Sup     : 1484
% 8.71/2.88  #Fact    : 2
% 8.71/2.88  #Define  : 0
% 8.71/2.88  #Split   : 3
% 8.71/2.88  #Chain   : 0
% 8.71/2.88  #Close   : 0
% 8.71/2.88  
% 8.71/2.88  Ordering : KBO
% 8.71/2.88  
% 8.71/2.88  Simplification rules
% 8.71/2.88  ----------------------
% 8.71/2.88  #Subsume      : 266
% 8.71/2.88  #Demod        : 593
% 8.71/2.88  #Tautology    : 420
% 8.71/2.88  #SimpNegUnit  : 44
% 8.71/2.88  #BackRed      : 20
% 8.71/2.88  
% 8.71/2.88  #Partial instantiations: 0
% 8.71/2.88  #Strategies tried      : 1
% 8.71/2.88  
% 8.71/2.88  Timing (in seconds)
% 8.71/2.88  ----------------------
% 8.95/2.88  Preprocessing        : 0.31
% 8.95/2.88  Parsing              : 0.16
% 8.95/2.88  CNF conversion       : 0.02
% 8.95/2.88  Main loop            : 1.76
% 8.95/2.88  Inferencing          : 0.54
% 8.95/2.88  Reduction            : 0.49
% 8.95/2.88  Demodulation         : 0.33
% 8.95/2.88  BG Simplification    : 0.08
% 8.95/2.88  Subsumption          : 0.54
% 8.95/2.88  Abstraction          : 0.08
% 8.95/2.88  MUC search           : 0.00
% 8.95/2.89  Cooper               : 0.00
% 8.95/2.89  Total                : 2.10
% 8.95/2.89  Index Insertion      : 0.00
% 8.95/2.89  Index Deletion       : 0.00
% 8.95/2.89  Index Matching       : 0.00
% 8.95/2.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
