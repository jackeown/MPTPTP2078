%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:52 EST 2020

% Result     : Theorem 8.32s
% Output     : CNFRefutation 8.58s
% Verified   : 
% Statistics : Number of formulae       :  177 (1265 expanded)
%              Number of leaves         :   53 ( 454 expanded)
%              Depth                    :   25
%              Number of atoms          :  443 (4350 expanded)
%              Number of equality atoms :   37 ( 309 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_subset_1 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m2_subset_1,type,(
    m2_subset_1: ( $i * $i * $i ) > $o )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_259,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v2_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_185,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ? [C] :
              ( ~ v2_struct_0(C)
              & v1_pre_topc(C)
              & m1_pre_topc(C,A)
              & B = u1_struct_0(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ? [C] : m2_subset_1(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ! [C] :
          ( m2_subset_1(C,A,B)
        <=> m1_subset_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_198,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_119,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_239,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_227,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( ( ~ v2_struct_0(C)
                    & v1_pre_topc(C)
                    & v1_tdlat_3(C)
                    & m1_pre_topc(C,A) )
                 => B != u1_struct_0(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_164,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(f_132,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

tff(f_150,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & v2_tdlat_3(A) )
       => ( ~ v2_struct_0(A)
          & v7_struct_0(A)
          & v2_pre_topc(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_82,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_88,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_86,plain,(
    v2_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_96,plain,
    ( v2_tex_2('#skF_8','#skF_7')
    | v1_zfmisc_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_100,plain,(
    v1_zfmisc_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_90,plain,
    ( ~ v1_zfmisc_1('#skF_8')
    | ~ v2_tex_2('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_102,plain,(
    ~ v2_tex_2('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_90])).

tff(c_78,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_997,plain,(
    ! [A_171,B_172] :
      ( ~ v2_struct_0('#skF_5'(A_171,B_172))
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0(A_171)))
      | v1_xboole_0(B_172)
      | ~ l1_pre_topc(A_171)
      | v2_struct_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_1019,plain,
    ( ~ v2_struct_0('#skF_5'('#skF_7','#skF_8'))
    | v1_xboole_0('#skF_8')
    | ~ l1_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_997])).

tff(c_1030,plain,
    ( ~ v2_struct_0('#skF_5'('#skF_7','#skF_8'))
    | v1_xboole_0('#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1019])).

tff(c_1031,plain,(
    ~ v2_struct_0('#skF_5'('#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_80,c_1030])).

tff(c_171,plain,(
    ! [B_86,A_87] :
      ( v1_xboole_0(B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_87))
      | ~ v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_178,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_78,c_171])).

tff(c_182,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_178])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( m2_subset_1('#skF_4'(A_20,B_21),A_20,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20))
      | v1_xboole_0(B_21)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_875,plain,(
    ! [C_157,B_158,A_159] :
      ( m1_subset_1(C_157,B_158)
      | ~ m2_subset_1(C_157,A_159,B_158)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(A_159))
      | v1_xboole_0(B_158)
      | v1_xboole_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_879,plain,(
    ! [A_160,B_161] :
      ( m1_subset_1('#skF_4'(A_160,B_161),B_161)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(A_160))
      | v1_xboole_0(B_161)
      | v1_xboole_0(A_160) ) ),
    inference(resolution,[status(thm)],[c_30,c_875])).

tff(c_28,plain,(
    ! [A_18,B_19] :
      ( r2_hidden(A_18,B_19)
      | v1_xboole_0(B_19)
      | ~ m1_subset_1(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_tarski(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k1_tarski(A_11),B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_252,plain,(
    ! [B_99,A_100] :
      ( B_99 = A_100
      | ~ r1_tarski(A_100,B_99)
      | ~ v1_zfmisc_1(B_99)
      | v1_xboole_0(B_99)
      | v1_xboole_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_255,plain,(
    ! [A_11,B_12] :
      ( k1_tarski(A_11) = B_12
      | ~ v1_zfmisc_1(B_12)
      | v1_xboole_0(B_12)
      | v1_xboole_0(k1_tarski(A_11))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_22,c_252])).

tff(c_259,plain,(
    ! [A_101,B_102] :
      ( k1_tarski(A_101) = B_102
      | ~ v1_zfmisc_1(B_102)
      | v1_xboole_0(B_102)
      | ~ r2_hidden(A_101,B_102) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_255])).

tff(c_269,plain,(
    ! [A_18,B_19] :
      ( k1_tarski(A_18) = B_19
      | ~ v1_zfmisc_1(B_19)
      | v1_xboole_0(B_19)
      | ~ m1_subset_1(A_18,B_19) ) ),
    inference(resolution,[status(thm)],[c_28,c_259])).

tff(c_1076,plain,(
    ! [A_175,B_176] :
      ( k1_tarski('#skF_4'(A_175,B_176)) = B_176
      | ~ v1_zfmisc_1(B_176)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(A_175))
      | v1_xboole_0(B_176)
      | v1_xboole_0(A_175) ) ),
    inference(resolution,[status(thm)],[c_879,c_269])).

tff(c_1102,plain,
    ( k1_tarski('#skF_4'(u1_struct_0('#skF_7'),'#skF_8')) = '#skF_8'
    | ~ v1_zfmisc_1('#skF_8')
    | v1_xboole_0('#skF_8')
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_78,c_1076])).

tff(c_1113,plain,
    ( k1_tarski('#skF_4'(u1_struct_0('#skF_7'),'#skF_8')) = '#skF_8'
    | v1_xboole_0('#skF_8')
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1102])).

tff(c_1114,plain,(
    k1_tarski('#skF_4'(u1_struct_0('#skF_7'),'#skF_8')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_80,c_1113])).

tff(c_121,plain,(
    ! [A_73] :
      ( v1_xboole_0(A_73)
      | r2_hidden('#skF_1'(A_73),A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [C_9,A_5] :
      ( C_9 = A_5
      | ~ r2_hidden(C_9,k1_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_125,plain,(
    ! [A_5] :
      ( '#skF_1'(k1_tarski(A_5)) = A_5
      | v1_xboole_0(k1_tarski(A_5)) ) ),
    inference(resolution,[status(thm)],[c_121,c_6])).

tff(c_131,plain,(
    ! [A_5] : '#skF_1'(k1_tarski(A_5)) = A_5 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_125])).

tff(c_8,plain,(
    ! [C_9] : r2_hidden(C_9,k1_tarski(C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_281,plain,(
    ! [A_105] :
      ( k1_tarski('#skF_1'(A_105)) = A_105
      | ~ v1_zfmisc_1(A_105)
      | v1_xboole_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_4,c_259])).

tff(c_371,plain,(
    ! [A_112,B_113] :
      ( r1_tarski(A_112,B_113)
      | ~ r2_hidden('#skF_1'(A_112),B_113)
      | ~ v1_zfmisc_1(A_112)
      | v1_xboole_0(A_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_22])).

tff(c_403,plain,(
    ! [A_115] :
      ( r1_tarski(A_115,k1_tarski('#skF_1'(A_115)))
      | ~ v1_zfmisc_1(A_115)
      | v1_xboole_0(A_115) ) ),
    inference(resolution,[status(thm)],[c_8,c_371])).

tff(c_416,plain,(
    ! [A_5] :
      ( r1_tarski(k1_tarski(A_5),k1_tarski(A_5))
      | ~ v1_zfmisc_1(k1_tarski(A_5))
      | v1_xboole_0(k1_tarski(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_403])).

tff(c_422,plain,(
    ! [A_5] :
      ( r1_tarski(k1_tarski(A_5),k1_tarski(A_5))
      | ~ v1_zfmisc_1(k1_tarski(A_5)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_416])).

tff(c_1133,plain,
    ( r1_tarski('#skF_8',k1_tarski('#skF_4'(u1_struct_0('#skF_7'),'#skF_8')))
    | ~ v1_zfmisc_1(k1_tarski('#skF_4'(u1_struct_0('#skF_7'),'#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1114,c_422])).

tff(c_1172,plain,(
    r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1114,c_1114,c_1133])).

tff(c_1532,plain,(
    ! [A_183,B_184] :
      ( u1_struct_0('#skF_5'(A_183,B_184)) = B_184
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0(A_183)))
      | v1_xboole_0(B_184)
      | ~ l1_pre_topc(A_183)
      | v2_struct_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_1558,plain,
    ( u1_struct_0('#skF_5'('#skF_7','#skF_8')) = '#skF_8'
    | v1_xboole_0('#skF_8')
    | ~ l1_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_1532])).

tff(c_1570,plain,
    ( u1_struct_0('#skF_5'('#skF_7','#skF_8')) = '#skF_8'
    | v1_xboole_0('#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1558])).

tff(c_1571,plain,(
    u1_struct_0('#skF_5'('#skF_7','#skF_8')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_80,c_1570])).

tff(c_1387,plain,(
    ! [A_179,B_180] :
      ( m1_pre_topc('#skF_5'(A_179,B_180),A_179)
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_179)))
      | v1_xboole_0(B_180)
      | ~ l1_pre_topc(A_179)
      | v2_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_1406,plain,
    ( m1_pre_topc('#skF_5'('#skF_7','#skF_8'),'#skF_7')
    | v1_xboole_0('#skF_8')
    | ~ l1_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_1387])).

tff(c_1418,plain,
    ( m1_pre_topc('#skF_5'('#skF_7','#skF_8'),'#skF_7')
    | v1_xboole_0('#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1406])).

tff(c_1419,plain,(
    m1_pre_topc('#skF_5'('#skF_7','#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_80,c_1418])).

tff(c_147,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1(A_75,B_76)
      | ~ r2_hidden(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_155,plain,(
    ! [C_9] : m1_subset_1(C_9,k1_tarski(C_9)) ),
    inference(resolution,[status(thm)],[c_8,c_147])).

tff(c_1151,plain,(
    m1_subset_1('#skF_4'(u1_struct_0('#skF_7'),'#skF_8'),'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1114,c_155])).

tff(c_183,plain,(
    ! [A_88,B_89] :
      ( r2_hidden(A_88,B_89)
      | v1_xboole_0(B_89)
      | ~ m1_subset_1(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_190,plain,(
    ! [A_88,A_5] :
      ( A_88 = A_5
      | v1_xboole_0(k1_tarski(A_5))
      | ~ m1_subset_1(A_88,k1_tarski(A_5)) ) ),
    inference(resolution,[status(thm)],[c_183,c_6])).

tff(c_197,plain,(
    ! [A_88,A_5] :
      ( A_88 = A_5
      | ~ m1_subset_1(A_88,k1_tarski(A_5)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_190])).

tff(c_290,plain,(
    ! [A_88,A_105] :
      ( A_88 = '#skF_1'(A_105)
      | ~ m1_subset_1(A_88,A_105)
      | ~ v1_zfmisc_1(A_105)
      | v1_xboole_0(A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_197])).

tff(c_1200,plain,
    ( '#skF_4'(u1_struct_0('#skF_7'),'#skF_8') = '#skF_1'('#skF_8')
    | ~ v1_zfmisc_1('#skF_8')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1151,c_290])).

tff(c_1209,plain,
    ( '#skF_4'(u1_struct_0('#skF_7'),'#skF_8') = '#skF_1'('#skF_8')
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1200])).

tff(c_1210,plain,(
    '#skF_4'(u1_struct_0('#skF_7'),'#skF_8') = '#skF_1'('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1209])).

tff(c_1219,plain,(
    k1_tarski('#skF_1'('#skF_8')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1210,c_1114])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | ~ r1_tarski(k1_tarski(A_11),B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_485,plain,(
    ! [A_122,B_123] :
      ( r2_hidden('#skF_1'(A_122),B_123)
      | ~ r1_tarski(A_122,B_123)
      | ~ v1_zfmisc_1(A_122)
      | v1_xboole_0(A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_20])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,B_17)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_534,plain,(
    ! [A_126,B_127] :
      ( m1_subset_1('#skF_1'(A_126),B_127)
      | ~ r1_tarski(A_126,B_127)
      | ~ v1_zfmisc_1(A_126)
      | v1_xboole_0(A_126) ) ),
    inference(resolution,[status(thm)],[c_485,c_26])).

tff(c_554,plain,(
    ! [A_5,B_127] :
      ( m1_subset_1(A_5,B_127)
      | ~ r1_tarski(k1_tarski(A_5),B_127)
      | ~ v1_zfmisc_1(k1_tarski(A_5))
      | v1_xboole_0(k1_tarski(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_534])).

tff(c_560,plain,(
    ! [A_5,B_127] :
      ( m1_subset_1(A_5,B_127)
      | ~ r1_tarski(k1_tarski(A_5),B_127)
      | ~ v1_zfmisc_1(k1_tarski(A_5)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_554])).

tff(c_1282,plain,(
    ! [B_127] :
      ( m1_subset_1('#skF_1'('#skF_8'),B_127)
      | ~ r1_tarski('#skF_8',B_127)
      | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_8'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1219,c_560])).

tff(c_1334,plain,(
    ! [B_127] :
      ( m1_subset_1('#skF_1'('#skF_8'),B_127)
      | ~ r1_tarski('#skF_8',B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1219,c_1282])).

tff(c_1807,plain,(
    ! [C_190,A_191,B_192] :
      ( m1_subset_1(C_190,u1_struct_0(A_191))
      | ~ m1_subset_1(C_190,u1_struct_0(B_192))
      | ~ m1_pre_topc(B_192,A_191)
      | v2_struct_0(B_192)
      | ~ l1_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6946,plain,(
    ! [A_374,B_375] :
      ( m1_subset_1('#skF_1'('#skF_8'),u1_struct_0(A_374))
      | ~ m1_pre_topc(B_375,A_374)
      | v2_struct_0(B_375)
      | ~ l1_pre_topc(A_374)
      | v2_struct_0(A_374)
      | ~ r1_tarski('#skF_8',u1_struct_0(B_375)) ) ),
    inference(resolution,[status(thm)],[c_1334,c_1807])).

tff(c_6952,plain,
    ( m1_subset_1('#skF_1'('#skF_8'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_5'('#skF_7','#skF_8'))
    | ~ l1_pre_topc('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ r1_tarski('#skF_8',u1_struct_0('#skF_5'('#skF_7','#skF_8'))) ),
    inference(resolution,[status(thm)],[c_1419,c_6946])).

tff(c_6960,plain,
    ( m1_subset_1('#skF_1'('#skF_8'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_5'('#skF_7','#skF_8'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1172,c_1571,c_82,c_6952])).

tff(c_6961,plain,(
    m1_subset_1('#skF_1'('#skF_8'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1031,c_6960])).

tff(c_44,plain,(
    ! [A_39,B_40] :
      ( k6_domain_1(A_39,B_40) = k1_tarski(B_40)
      | ~ m1_subset_1(B_40,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_6985,plain,
    ( k6_domain_1(u1_struct_0('#skF_7'),'#skF_1'('#skF_8')) = k1_tarski('#skF_1'('#skF_8'))
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_6961,c_44])).

tff(c_7011,plain,
    ( k6_domain_1(u1_struct_0('#skF_7'),'#skF_1'('#skF_8')) = '#skF_8'
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_6985])).

tff(c_7012,plain,(
    k6_domain_1(u1_struct_0('#skF_7'),'#skF_1'('#skF_8')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_7011])).

tff(c_76,plain,(
    ! [A_61,B_63] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_61),B_63),A_61)
      | ~ m1_subset_1(B_63,u1_struct_0(A_61))
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_7119,plain,
    ( v2_tex_2('#skF_8','#skF_7')
    | ~ m1_subset_1('#skF_1'('#skF_8'),u1_struct_0('#skF_7'))
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_7012,c_76])).

tff(c_7144,plain,
    ( v2_tex_2('#skF_8','#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_6961,c_7119])).

tff(c_7146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_102,c_7144])).

tff(c_7147,plain,(
    v2_tex_2('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_9214,plain,(
    ! [A_560,B_561] :
      ( m1_pre_topc('#skF_6'(A_560,B_561),A_560)
      | ~ v2_tex_2(B_561,A_560)
      | ~ m1_subset_1(B_561,k1_zfmisc_1(u1_struct_0(A_560)))
      | v1_xboole_0(B_561)
      | ~ l1_pre_topc(A_560)
      | ~ v2_pre_topc(A_560)
      | v2_struct_0(A_560) ) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_9239,plain,
    ( m1_pre_topc('#skF_6'('#skF_7','#skF_8'),'#skF_7')
    | ~ v2_tex_2('#skF_8','#skF_7')
    | v1_xboole_0('#skF_8')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_9214])).

tff(c_9254,plain,
    ( m1_pre_topc('#skF_6'('#skF_7','#skF_8'),'#skF_7')
    | v1_xboole_0('#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_7147,c_9239])).

tff(c_9255,plain,(
    m1_pre_topc('#skF_6'('#skF_7','#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_80,c_9254])).

tff(c_38,plain,(
    ! [B_30,A_28] :
      ( l1_pre_topc(B_30)
      | ~ m1_pre_topc(B_30,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_9261,plain,
    ( l1_pre_topc('#skF_6'('#skF_7','#skF_8'))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_9255,c_38])).

tff(c_9268,plain,(
    l1_pre_topc('#skF_6'('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_9261])).

tff(c_36,plain,(
    ! [A_27] :
      ( l1_struct_0(A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_8913,plain,(
    ! [A_547,B_548] :
      ( ~ v2_struct_0('#skF_6'(A_547,B_548))
      | ~ v2_tex_2(B_548,A_547)
      | ~ m1_subset_1(B_548,k1_zfmisc_1(u1_struct_0(A_547)))
      | v1_xboole_0(B_548)
      | ~ l1_pre_topc(A_547)
      | ~ v2_pre_topc(A_547)
      | v2_struct_0(A_547) ) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_8945,plain,
    ( ~ v2_struct_0('#skF_6'('#skF_7','#skF_8'))
    | ~ v2_tex_2('#skF_8','#skF_7')
    | v1_xboole_0('#skF_8')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_8913])).

tff(c_8960,plain,
    ( ~ v2_struct_0('#skF_6'('#skF_7','#skF_8'))
    | v1_xboole_0('#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_7147,c_8945])).

tff(c_8961,plain,(
    ~ v2_struct_0('#skF_6'('#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_80,c_8960])).

tff(c_84,plain,(
    v2_tdlat_3('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_54,plain,(
    ! [B_45,A_43] :
      ( v2_tdlat_3(B_45)
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43)
      | ~ v2_tdlat_3(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_9258,plain,
    ( v2_tdlat_3('#skF_6'('#skF_7','#skF_8'))
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_tdlat_3('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_9255,c_54])).

tff(c_9264,plain,
    ( v2_tdlat_3('#skF_6'('#skF_7','#skF_8'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_9258])).

tff(c_9265,plain,(
    v2_tdlat_3('#skF_6'('#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_9264])).

tff(c_46,plain,(
    ! [A_41] :
      ( v2_pre_topc(A_41)
      | ~ v2_tdlat_3(A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_9272,plain,
    ( v2_pre_topc('#skF_6'('#skF_7','#skF_8'))
    | ~ l1_pre_topc('#skF_6'('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_9265,c_46])).

tff(c_9283,plain,(
    v2_pre_topc('#skF_6'('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9268,c_9272])).

tff(c_8602,plain,(
    ! [A_523,B_524] :
      ( v1_tdlat_3('#skF_6'(A_523,B_524))
      | ~ v2_tex_2(B_524,A_523)
      | ~ m1_subset_1(B_524,k1_zfmisc_1(u1_struct_0(A_523)))
      | v1_xboole_0(B_524)
      | ~ l1_pre_topc(A_523)
      | ~ v2_pre_topc(A_523)
      | v2_struct_0(A_523) ) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_8631,plain,
    ( v1_tdlat_3('#skF_6'('#skF_7','#skF_8'))
    | ~ v2_tex_2('#skF_8','#skF_7')
    | v1_xboole_0('#skF_8')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_8602])).

tff(c_8646,plain,
    ( v1_tdlat_3('#skF_6'('#skF_7','#skF_8'))
    | v1_xboole_0('#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_7147,c_8631])).

tff(c_8647,plain,(
    v1_tdlat_3('#skF_6'('#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_80,c_8646])).

tff(c_50,plain,(
    ! [A_42] :
      ( v7_struct_0(A_42)
      | ~ v2_tdlat_3(A_42)
      | ~ v1_tdlat_3(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_7148,plain,(
    ~ v1_zfmisc_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_9401,plain,(
    ! [A_568,B_569] :
      ( u1_struct_0('#skF_6'(A_568,B_569)) = B_569
      | ~ v2_tex_2(B_569,A_568)
      | ~ m1_subset_1(B_569,k1_zfmisc_1(u1_struct_0(A_568)))
      | v1_xboole_0(B_569)
      | ~ l1_pre_topc(A_568)
      | ~ v2_pre_topc(A_568)
      | v2_struct_0(A_568) ) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_9436,plain,
    ( u1_struct_0('#skF_6'('#skF_7','#skF_8')) = '#skF_8'
    | ~ v2_tex_2('#skF_8','#skF_7')
    | v1_xboole_0('#skF_8')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_9401])).

tff(c_9451,plain,
    ( u1_struct_0('#skF_6'('#skF_7','#skF_8')) = '#skF_8'
    | v1_xboole_0('#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_7147,c_9436])).

tff(c_9452,plain,(
    u1_struct_0('#skF_6'('#skF_7','#skF_8')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_80,c_9451])).

tff(c_40,plain,(
    ! [A_31] :
      ( v1_zfmisc_1(u1_struct_0(A_31))
      | ~ l1_struct_0(A_31)
      | ~ v7_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_9501,plain,
    ( v1_zfmisc_1('#skF_8')
    | ~ l1_struct_0('#skF_6'('#skF_7','#skF_8'))
    | ~ v7_struct_0('#skF_6'('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9452,c_40])).

tff(c_9548,plain,
    ( ~ l1_struct_0('#skF_6'('#skF_7','#skF_8'))
    | ~ v7_struct_0('#skF_6'('#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_7148,c_9501])).

tff(c_9550,plain,(
    ~ v7_struct_0('#skF_6'('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_9548])).

tff(c_9553,plain,
    ( ~ v2_tdlat_3('#skF_6'('#skF_7','#skF_8'))
    | ~ v1_tdlat_3('#skF_6'('#skF_7','#skF_8'))
    | ~ v2_pre_topc('#skF_6'('#skF_7','#skF_8'))
    | v2_struct_0('#skF_6'('#skF_7','#skF_8'))
    | ~ l1_pre_topc('#skF_6'('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_50,c_9550])).

tff(c_9556,plain,(
    v2_struct_0('#skF_6'('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9268,c_9283,c_8647,c_9265,c_9553])).

tff(c_9558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8961,c_9556])).

tff(c_9559,plain,(
    ~ l1_struct_0('#skF_6'('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_9548])).

tff(c_9602,plain,(
    ~ l1_pre_topc('#skF_6'('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_36,c_9559])).

tff(c_9606,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9268,c_9602])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.32/2.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.54/3.00  
% 8.54/3.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.54/3.00  %$ m2_subset_1 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 8.54/3.00  
% 8.54/3.00  %Foreground sorts:
% 8.54/3.00  
% 8.54/3.00  
% 8.54/3.00  %Background operators:
% 8.54/3.00  
% 8.54/3.00  
% 8.54/3.00  %Foreground operators:
% 8.54/3.00  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.54/3.00  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.54/3.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.54/3.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.54/3.00  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.54/3.00  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.54/3.00  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 8.54/3.00  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.54/3.00  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 8.54/3.00  tff('#skF_7', type, '#skF_7': $i).
% 8.54/3.00  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.54/3.00  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 8.54/3.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.54/3.00  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 8.54/3.00  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.54/3.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.54/3.00  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.54/3.00  tff('#skF_8', type, '#skF_8': $i).
% 8.54/3.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.54/3.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.54/3.00  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.54/3.00  tff(m2_subset_1, type, m2_subset_1: ($i * $i * $i) > $o).
% 8.54/3.00  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 8.54/3.00  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.54/3.00  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.54/3.00  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.54/3.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.54/3.00  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.54/3.00  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.54/3.00  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 8.54/3.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.54/3.00  
% 8.58/3.02  tff(f_259, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 8.58/3.02  tff(f_185, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tsep_1)).
% 8.58/3.02  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 8.58/3.02  tff(f_73, axiom, (![A, B]: (((~v1_xboole_0(A) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(A))) => (?[C]: m2_subset_1(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m2_subset_1)).
% 8.58/3.02  tff(f_86, axiom, (![A, B]: (((~v1_xboole_0(A) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(A))) => (![C]: (m2_subset_1(C, A, B) <=> m1_subset_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_m2_subset_1)).
% 8.58/3.02  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 8.58/3.02  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 8.58/3.02  tff(f_45, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 8.58/3.02  tff(f_198, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 8.58/3.02  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.58/3.02  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 8.58/3.02  tff(f_56, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 8.58/3.02  tff(f_119, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 8.58/3.02  tff(f_126, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 8.58/3.02  tff(f_239, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 8.58/3.02  tff(f_227, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 8.58/3.02  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 8.58/3.02  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.58/3.02  tff(f_164, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 8.58/3.02  tff(f_132, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 8.58/3.02  tff(f_150, axiom, (![A]: (l1_pre_topc(A) => ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A)) => ((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_1)).
% 8.58/3.02  tff(f_103, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 8.58/3.02  tff(c_82, plain, (l1_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_259])).
% 8.58/3.02  tff(c_88, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_259])).
% 8.58/3.02  tff(c_80, plain, (~v1_xboole_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_259])).
% 8.58/3.02  tff(c_86, plain, (v2_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_259])).
% 8.58/3.02  tff(c_96, plain, (v2_tex_2('#skF_8', '#skF_7') | v1_zfmisc_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_259])).
% 8.58/3.02  tff(c_100, plain, (v1_zfmisc_1('#skF_8')), inference(splitLeft, [status(thm)], [c_96])).
% 8.58/3.02  tff(c_90, plain, (~v1_zfmisc_1('#skF_8') | ~v2_tex_2('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_259])).
% 8.58/3.02  tff(c_102, plain, (~v2_tex_2('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_90])).
% 8.58/3.02  tff(c_78, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_259])).
% 8.58/3.02  tff(c_997, plain, (![A_171, B_172]: (~v2_struct_0('#skF_5'(A_171, B_172)) | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0(A_171))) | v1_xboole_0(B_172) | ~l1_pre_topc(A_171) | v2_struct_0(A_171))), inference(cnfTransformation, [status(thm)], [f_185])).
% 8.58/3.02  tff(c_1019, plain, (~v2_struct_0('#skF_5'('#skF_7', '#skF_8')) | v1_xboole_0('#skF_8') | ~l1_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_78, c_997])).
% 8.58/3.02  tff(c_1030, plain, (~v2_struct_0('#skF_5'('#skF_7', '#skF_8')) | v1_xboole_0('#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1019])).
% 8.58/3.02  tff(c_1031, plain, (~v2_struct_0('#skF_5'('#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_88, c_80, c_1030])).
% 8.58/3.02  tff(c_171, plain, (![B_86, A_87]: (v1_xboole_0(B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_87)) | ~v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.58/3.02  tff(c_178, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_78, c_171])).
% 8.58/3.02  tff(c_182, plain, (~v1_xboole_0(u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_80, c_178])).
% 8.58/3.02  tff(c_30, plain, (![A_20, B_21]: (m2_subset_1('#skF_4'(A_20, B_21), A_20, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)) | v1_xboole_0(B_21) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.58/3.02  tff(c_875, plain, (![C_157, B_158, A_159]: (m1_subset_1(C_157, B_158) | ~m2_subset_1(C_157, A_159, B_158) | ~m1_subset_1(B_158, k1_zfmisc_1(A_159)) | v1_xboole_0(B_158) | v1_xboole_0(A_159))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.58/3.02  tff(c_879, plain, (![A_160, B_161]: (m1_subset_1('#skF_4'(A_160, B_161), B_161) | ~m1_subset_1(B_161, k1_zfmisc_1(A_160)) | v1_xboole_0(B_161) | v1_xboole_0(A_160))), inference(resolution, [status(thm)], [c_30, c_875])).
% 8.58/3.02  tff(c_28, plain, (![A_18, B_19]: (r2_hidden(A_18, B_19) | v1_xboole_0(B_19) | ~m1_subset_1(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.58/3.02  tff(c_18, plain, (![A_10]: (~v1_xboole_0(k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.58/3.02  tff(c_22, plain, (![A_11, B_12]: (r1_tarski(k1_tarski(A_11), B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.58/3.02  tff(c_252, plain, (![B_99, A_100]: (B_99=A_100 | ~r1_tarski(A_100, B_99) | ~v1_zfmisc_1(B_99) | v1_xboole_0(B_99) | v1_xboole_0(A_100))), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.58/3.02  tff(c_255, plain, (![A_11, B_12]: (k1_tarski(A_11)=B_12 | ~v1_zfmisc_1(B_12) | v1_xboole_0(B_12) | v1_xboole_0(k1_tarski(A_11)) | ~r2_hidden(A_11, B_12))), inference(resolution, [status(thm)], [c_22, c_252])).
% 8.58/3.02  tff(c_259, plain, (![A_101, B_102]: (k1_tarski(A_101)=B_102 | ~v1_zfmisc_1(B_102) | v1_xboole_0(B_102) | ~r2_hidden(A_101, B_102))), inference(negUnitSimplification, [status(thm)], [c_18, c_255])).
% 8.58/3.02  tff(c_269, plain, (![A_18, B_19]: (k1_tarski(A_18)=B_19 | ~v1_zfmisc_1(B_19) | v1_xboole_0(B_19) | ~m1_subset_1(A_18, B_19))), inference(resolution, [status(thm)], [c_28, c_259])).
% 8.58/3.02  tff(c_1076, plain, (![A_175, B_176]: (k1_tarski('#skF_4'(A_175, B_176))=B_176 | ~v1_zfmisc_1(B_176) | ~m1_subset_1(B_176, k1_zfmisc_1(A_175)) | v1_xboole_0(B_176) | v1_xboole_0(A_175))), inference(resolution, [status(thm)], [c_879, c_269])).
% 8.58/3.02  tff(c_1102, plain, (k1_tarski('#skF_4'(u1_struct_0('#skF_7'), '#skF_8'))='#skF_8' | ~v1_zfmisc_1('#skF_8') | v1_xboole_0('#skF_8') | v1_xboole_0(u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_78, c_1076])).
% 8.58/3.02  tff(c_1113, plain, (k1_tarski('#skF_4'(u1_struct_0('#skF_7'), '#skF_8'))='#skF_8' | v1_xboole_0('#skF_8') | v1_xboole_0(u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1102])).
% 8.58/3.02  tff(c_1114, plain, (k1_tarski('#skF_4'(u1_struct_0('#skF_7'), '#skF_8'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_182, c_80, c_1113])).
% 8.58/3.02  tff(c_121, plain, (![A_73]: (v1_xboole_0(A_73) | r2_hidden('#skF_1'(A_73), A_73))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.58/3.02  tff(c_6, plain, (![C_9, A_5]: (C_9=A_5 | ~r2_hidden(C_9, k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.58/3.02  tff(c_125, plain, (![A_5]: ('#skF_1'(k1_tarski(A_5))=A_5 | v1_xboole_0(k1_tarski(A_5)))), inference(resolution, [status(thm)], [c_121, c_6])).
% 8.58/3.02  tff(c_131, plain, (![A_5]: ('#skF_1'(k1_tarski(A_5))=A_5)), inference(negUnitSimplification, [status(thm)], [c_18, c_125])).
% 8.58/3.02  tff(c_8, plain, (![C_9]: (r2_hidden(C_9, k1_tarski(C_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.58/3.02  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.58/3.02  tff(c_281, plain, (![A_105]: (k1_tarski('#skF_1'(A_105))=A_105 | ~v1_zfmisc_1(A_105) | v1_xboole_0(A_105))), inference(resolution, [status(thm)], [c_4, c_259])).
% 8.58/3.02  tff(c_371, plain, (![A_112, B_113]: (r1_tarski(A_112, B_113) | ~r2_hidden('#skF_1'(A_112), B_113) | ~v1_zfmisc_1(A_112) | v1_xboole_0(A_112))), inference(superposition, [status(thm), theory('equality')], [c_281, c_22])).
% 8.58/3.02  tff(c_403, plain, (![A_115]: (r1_tarski(A_115, k1_tarski('#skF_1'(A_115))) | ~v1_zfmisc_1(A_115) | v1_xboole_0(A_115))), inference(resolution, [status(thm)], [c_8, c_371])).
% 8.58/3.02  tff(c_416, plain, (![A_5]: (r1_tarski(k1_tarski(A_5), k1_tarski(A_5)) | ~v1_zfmisc_1(k1_tarski(A_5)) | v1_xboole_0(k1_tarski(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_131, c_403])).
% 8.58/3.02  tff(c_422, plain, (![A_5]: (r1_tarski(k1_tarski(A_5), k1_tarski(A_5)) | ~v1_zfmisc_1(k1_tarski(A_5)))), inference(negUnitSimplification, [status(thm)], [c_18, c_416])).
% 8.58/3.02  tff(c_1133, plain, (r1_tarski('#skF_8', k1_tarski('#skF_4'(u1_struct_0('#skF_7'), '#skF_8'))) | ~v1_zfmisc_1(k1_tarski('#skF_4'(u1_struct_0('#skF_7'), '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_1114, c_422])).
% 8.58/3.02  tff(c_1172, plain, (r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1114, c_1114, c_1133])).
% 8.58/3.02  tff(c_1532, plain, (![A_183, B_184]: (u1_struct_0('#skF_5'(A_183, B_184))=B_184 | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0(A_183))) | v1_xboole_0(B_184) | ~l1_pre_topc(A_183) | v2_struct_0(A_183))), inference(cnfTransformation, [status(thm)], [f_185])).
% 8.58/3.02  tff(c_1558, plain, (u1_struct_0('#skF_5'('#skF_7', '#skF_8'))='#skF_8' | v1_xboole_0('#skF_8') | ~l1_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_78, c_1532])).
% 8.58/3.02  tff(c_1570, plain, (u1_struct_0('#skF_5'('#skF_7', '#skF_8'))='#skF_8' | v1_xboole_0('#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1558])).
% 8.58/3.02  tff(c_1571, plain, (u1_struct_0('#skF_5'('#skF_7', '#skF_8'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_88, c_80, c_1570])).
% 8.58/3.02  tff(c_1387, plain, (![A_179, B_180]: (m1_pre_topc('#skF_5'(A_179, B_180), A_179) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(A_179))) | v1_xboole_0(B_180) | ~l1_pre_topc(A_179) | v2_struct_0(A_179))), inference(cnfTransformation, [status(thm)], [f_185])).
% 8.58/3.02  tff(c_1406, plain, (m1_pre_topc('#skF_5'('#skF_7', '#skF_8'), '#skF_7') | v1_xboole_0('#skF_8') | ~l1_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_78, c_1387])).
% 8.58/3.02  tff(c_1418, plain, (m1_pre_topc('#skF_5'('#skF_7', '#skF_8'), '#skF_7') | v1_xboole_0('#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1406])).
% 8.58/3.02  tff(c_1419, plain, (m1_pre_topc('#skF_5'('#skF_7', '#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_88, c_80, c_1418])).
% 8.58/3.02  tff(c_147, plain, (![A_75, B_76]: (m1_subset_1(A_75, B_76) | ~r2_hidden(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.58/3.02  tff(c_155, plain, (![C_9]: (m1_subset_1(C_9, k1_tarski(C_9)))), inference(resolution, [status(thm)], [c_8, c_147])).
% 8.58/3.02  tff(c_1151, plain, (m1_subset_1('#skF_4'(u1_struct_0('#skF_7'), '#skF_8'), '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1114, c_155])).
% 8.58/3.02  tff(c_183, plain, (![A_88, B_89]: (r2_hidden(A_88, B_89) | v1_xboole_0(B_89) | ~m1_subset_1(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.58/3.02  tff(c_190, plain, (![A_88, A_5]: (A_88=A_5 | v1_xboole_0(k1_tarski(A_5)) | ~m1_subset_1(A_88, k1_tarski(A_5)))), inference(resolution, [status(thm)], [c_183, c_6])).
% 8.58/3.02  tff(c_197, plain, (![A_88, A_5]: (A_88=A_5 | ~m1_subset_1(A_88, k1_tarski(A_5)))), inference(negUnitSimplification, [status(thm)], [c_18, c_190])).
% 8.58/3.02  tff(c_290, plain, (![A_88, A_105]: (A_88='#skF_1'(A_105) | ~m1_subset_1(A_88, A_105) | ~v1_zfmisc_1(A_105) | v1_xboole_0(A_105))), inference(superposition, [status(thm), theory('equality')], [c_281, c_197])).
% 8.58/3.02  tff(c_1200, plain, ('#skF_4'(u1_struct_0('#skF_7'), '#skF_8')='#skF_1'('#skF_8') | ~v1_zfmisc_1('#skF_8') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_1151, c_290])).
% 8.58/3.02  tff(c_1209, plain, ('#skF_4'(u1_struct_0('#skF_7'), '#skF_8')='#skF_1'('#skF_8') | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1200])).
% 8.58/3.02  tff(c_1210, plain, ('#skF_4'(u1_struct_0('#skF_7'), '#skF_8')='#skF_1'('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_80, c_1209])).
% 8.58/3.02  tff(c_1219, plain, (k1_tarski('#skF_1'('#skF_8'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1210, c_1114])).
% 8.58/3.02  tff(c_20, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | ~r1_tarski(k1_tarski(A_11), B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.58/3.02  tff(c_485, plain, (![A_122, B_123]: (r2_hidden('#skF_1'(A_122), B_123) | ~r1_tarski(A_122, B_123) | ~v1_zfmisc_1(A_122) | v1_xboole_0(A_122))), inference(superposition, [status(thm), theory('equality')], [c_281, c_20])).
% 8.58/3.02  tff(c_26, plain, (![A_16, B_17]: (m1_subset_1(A_16, B_17) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.58/3.02  tff(c_534, plain, (![A_126, B_127]: (m1_subset_1('#skF_1'(A_126), B_127) | ~r1_tarski(A_126, B_127) | ~v1_zfmisc_1(A_126) | v1_xboole_0(A_126))), inference(resolution, [status(thm)], [c_485, c_26])).
% 8.58/3.02  tff(c_554, plain, (![A_5, B_127]: (m1_subset_1(A_5, B_127) | ~r1_tarski(k1_tarski(A_5), B_127) | ~v1_zfmisc_1(k1_tarski(A_5)) | v1_xboole_0(k1_tarski(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_131, c_534])).
% 8.58/3.02  tff(c_560, plain, (![A_5, B_127]: (m1_subset_1(A_5, B_127) | ~r1_tarski(k1_tarski(A_5), B_127) | ~v1_zfmisc_1(k1_tarski(A_5)))), inference(negUnitSimplification, [status(thm)], [c_18, c_554])).
% 8.58/3.02  tff(c_1282, plain, (![B_127]: (m1_subset_1('#skF_1'('#skF_8'), B_127) | ~r1_tarski('#skF_8', B_127) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_8'))))), inference(superposition, [status(thm), theory('equality')], [c_1219, c_560])).
% 8.58/3.02  tff(c_1334, plain, (![B_127]: (m1_subset_1('#skF_1'('#skF_8'), B_127) | ~r1_tarski('#skF_8', B_127))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1219, c_1282])).
% 8.58/3.02  tff(c_1807, plain, (![C_190, A_191, B_192]: (m1_subset_1(C_190, u1_struct_0(A_191)) | ~m1_subset_1(C_190, u1_struct_0(B_192)) | ~m1_pre_topc(B_192, A_191) | v2_struct_0(B_192) | ~l1_pre_topc(A_191) | v2_struct_0(A_191))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.58/3.02  tff(c_6946, plain, (![A_374, B_375]: (m1_subset_1('#skF_1'('#skF_8'), u1_struct_0(A_374)) | ~m1_pre_topc(B_375, A_374) | v2_struct_0(B_375) | ~l1_pre_topc(A_374) | v2_struct_0(A_374) | ~r1_tarski('#skF_8', u1_struct_0(B_375)))), inference(resolution, [status(thm)], [c_1334, c_1807])).
% 8.58/3.02  tff(c_6952, plain, (m1_subset_1('#skF_1'('#skF_8'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_5'('#skF_7', '#skF_8')) | ~l1_pre_topc('#skF_7') | v2_struct_0('#skF_7') | ~r1_tarski('#skF_8', u1_struct_0('#skF_5'('#skF_7', '#skF_8')))), inference(resolution, [status(thm)], [c_1419, c_6946])).
% 8.58/3.02  tff(c_6960, plain, (m1_subset_1('#skF_1'('#skF_8'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_5'('#skF_7', '#skF_8')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1172, c_1571, c_82, c_6952])).
% 8.58/3.02  tff(c_6961, plain, (m1_subset_1('#skF_1'('#skF_8'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_88, c_1031, c_6960])).
% 8.58/3.02  tff(c_44, plain, (![A_39, B_40]: (k6_domain_1(A_39, B_40)=k1_tarski(B_40) | ~m1_subset_1(B_40, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.58/3.02  tff(c_6985, plain, (k6_domain_1(u1_struct_0('#skF_7'), '#skF_1'('#skF_8'))=k1_tarski('#skF_1'('#skF_8')) | v1_xboole_0(u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_6961, c_44])).
% 8.58/3.02  tff(c_7011, plain, (k6_domain_1(u1_struct_0('#skF_7'), '#skF_1'('#skF_8'))='#skF_8' | v1_xboole_0(u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1219, c_6985])).
% 8.58/3.02  tff(c_7012, plain, (k6_domain_1(u1_struct_0('#skF_7'), '#skF_1'('#skF_8'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_182, c_7011])).
% 8.58/3.02  tff(c_76, plain, (![A_61, B_63]: (v2_tex_2(k6_domain_1(u1_struct_0(A_61), B_63), A_61) | ~m1_subset_1(B_63, u1_struct_0(A_61)) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_239])).
% 8.58/3.02  tff(c_7119, plain, (v2_tex_2('#skF_8', '#skF_7') | ~m1_subset_1('#skF_1'('#skF_8'), u1_struct_0('#skF_7')) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_7012, c_76])).
% 8.58/3.02  tff(c_7144, plain, (v2_tex_2('#skF_8', '#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_6961, c_7119])).
% 8.58/3.02  tff(c_7146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_102, c_7144])).
% 8.58/3.02  tff(c_7147, plain, (v2_tex_2('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_96])).
% 8.58/3.02  tff(c_9214, plain, (![A_560, B_561]: (m1_pre_topc('#skF_6'(A_560, B_561), A_560) | ~v2_tex_2(B_561, A_560) | ~m1_subset_1(B_561, k1_zfmisc_1(u1_struct_0(A_560))) | v1_xboole_0(B_561) | ~l1_pre_topc(A_560) | ~v2_pre_topc(A_560) | v2_struct_0(A_560))), inference(cnfTransformation, [status(thm)], [f_227])).
% 8.58/3.02  tff(c_9239, plain, (m1_pre_topc('#skF_6'('#skF_7', '#skF_8'), '#skF_7') | ~v2_tex_2('#skF_8', '#skF_7') | v1_xboole_0('#skF_8') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_78, c_9214])).
% 8.58/3.02  tff(c_9254, plain, (m1_pre_topc('#skF_6'('#skF_7', '#skF_8'), '#skF_7') | v1_xboole_0('#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_7147, c_9239])).
% 8.58/3.02  tff(c_9255, plain, (m1_pre_topc('#skF_6'('#skF_7', '#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_88, c_80, c_9254])).
% 8.58/3.02  tff(c_38, plain, (![B_30, A_28]: (l1_pre_topc(B_30) | ~m1_pre_topc(B_30, A_28) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.58/3.02  tff(c_9261, plain, (l1_pre_topc('#skF_6'('#skF_7', '#skF_8')) | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_9255, c_38])).
% 8.58/3.02  tff(c_9268, plain, (l1_pre_topc('#skF_6'('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_9261])).
% 8.58/3.02  tff(c_36, plain, (![A_27]: (l1_struct_0(A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.58/3.02  tff(c_8913, plain, (![A_547, B_548]: (~v2_struct_0('#skF_6'(A_547, B_548)) | ~v2_tex_2(B_548, A_547) | ~m1_subset_1(B_548, k1_zfmisc_1(u1_struct_0(A_547))) | v1_xboole_0(B_548) | ~l1_pre_topc(A_547) | ~v2_pre_topc(A_547) | v2_struct_0(A_547))), inference(cnfTransformation, [status(thm)], [f_227])).
% 8.58/3.02  tff(c_8945, plain, (~v2_struct_0('#skF_6'('#skF_7', '#skF_8')) | ~v2_tex_2('#skF_8', '#skF_7') | v1_xboole_0('#skF_8') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_78, c_8913])).
% 8.58/3.02  tff(c_8960, plain, (~v2_struct_0('#skF_6'('#skF_7', '#skF_8')) | v1_xboole_0('#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_7147, c_8945])).
% 8.58/3.02  tff(c_8961, plain, (~v2_struct_0('#skF_6'('#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_88, c_80, c_8960])).
% 8.58/3.02  tff(c_84, plain, (v2_tdlat_3('#skF_7')), inference(cnfTransformation, [status(thm)], [f_259])).
% 8.58/3.02  tff(c_54, plain, (![B_45, A_43]: (v2_tdlat_3(B_45) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43) | ~v2_tdlat_3(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_164])).
% 8.58/3.02  tff(c_9258, plain, (v2_tdlat_3('#skF_6'('#skF_7', '#skF_8')) | ~l1_pre_topc('#skF_7') | ~v2_tdlat_3('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_9255, c_54])).
% 8.58/3.02  tff(c_9264, plain, (v2_tdlat_3('#skF_6'('#skF_7', '#skF_8')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_9258])).
% 8.58/3.02  tff(c_9265, plain, (v2_tdlat_3('#skF_6'('#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_88, c_9264])).
% 8.58/3.02  tff(c_46, plain, (![A_41]: (v2_pre_topc(A_41) | ~v2_tdlat_3(A_41) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.58/3.02  tff(c_9272, plain, (v2_pre_topc('#skF_6'('#skF_7', '#skF_8')) | ~l1_pre_topc('#skF_6'('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_9265, c_46])).
% 8.58/3.02  tff(c_9283, plain, (v2_pre_topc('#skF_6'('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_9268, c_9272])).
% 8.58/3.02  tff(c_8602, plain, (![A_523, B_524]: (v1_tdlat_3('#skF_6'(A_523, B_524)) | ~v2_tex_2(B_524, A_523) | ~m1_subset_1(B_524, k1_zfmisc_1(u1_struct_0(A_523))) | v1_xboole_0(B_524) | ~l1_pre_topc(A_523) | ~v2_pre_topc(A_523) | v2_struct_0(A_523))), inference(cnfTransformation, [status(thm)], [f_227])).
% 8.58/3.02  tff(c_8631, plain, (v1_tdlat_3('#skF_6'('#skF_7', '#skF_8')) | ~v2_tex_2('#skF_8', '#skF_7') | v1_xboole_0('#skF_8') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_78, c_8602])).
% 8.58/3.02  tff(c_8646, plain, (v1_tdlat_3('#skF_6'('#skF_7', '#skF_8')) | v1_xboole_0('#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_7147, c_8631])).
% 8.58/3.02  tff(c_8647, plain, (v1_tdlat_3('#skF_6'('#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_88, c_80, c_8646])).
% 8.58/3.02  tff(c_50, plain, (![A_42]: (v7_struct_0(A_42) | ~v2_tdlat_3(A_42) | ~v1_tdlat_3(A_42) | ~v2_pre_topc(A_42) | v2_struct_0(A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.58/3.02  tff(c_7148, plain, (~v1_zfmisc_1('#skF_8')), inference(splitRight, [status(thm)], [c_96])).
% 8.58/3.02  tff(c_9401, plain, (![A_568, B_569]: (u1_struct_0('#skF_6'(A_568, B_569))=B_569 | ~v2_tex_2(B_569, A_568) | ~m1_subset_1(B_569, k1_zfmisc_1(u1_struct_0(A_568))) | v1_xboole_0(B_569) | ~l1_pre_topc(A_568) | ~v2_pre_topc(A_568) | v2_struct_0(A_568))), inference(cnfTransformation, [status(thm)], [f_227])).
% 8.58/3.02  tff(c_9436, plain, (u1_struct_0('#skF_6'('#skF_7', '#skF_8'))='#skF_8' | ~v2_tex_2('#skF_8', '#skF_7') | v1_xboole_0('#skF_8') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_78, c_9401])).
% 8.58/3.02  tff(c_9451, plain, (u1_struct_0('#skF_6'('#skF_7', '#skF_8'))='#skF_8' | v1_xboole_0('#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_7147, c_9436])).
% 8.58/3.02  tff(c_9452, plain, (u1_struct_0('#skF_6'('#skF_7', '#skF_8'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_88, c_80, c_9451])).
% 8.58/3.02  tff(c_40, plain, (![A_31]: (v1_zfmisc_1(u1_struct_0(A_31)) | ~l1_struct_0(A_31) | ~v7_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.58/3.02  tff(c_9501, plain, (v1_zfmisc_1('#skF_8') | ~l1_struct_0('#skF_6'('#skF_7', '#skF_8')) | ~v7_struct_0('#skF_6'('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_9452, c_40])).
% 8.58/3.02  tff(c_9548, plain, (~l1_struct_0('#skF_6'('#skF_7', '#skF_8')) | ~v7_struct_0('#skF_6'('#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_7148, c_9501])).
% 8.58/3.02  tff(c_9550, plain, (~v7_struct_0('#skF_6'('#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_9548])).
% 8.58/3.02  tff(c_9553, plain, (~v2_tdlat_3('#skF_6'('#skF_7', '#skF_8')) | ~v1_tdlat_3('#skF_6'('#skF_7', '#skF_8')) | ~v2_pre_topc('#skF_6'('#skF_7', '#skF_8')) | v2_struct_0('#skF_6'('#skF_7', '#skF_8')) | ~l1_pre_topc('#skF_6'('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_50, c_9550])).
% 8.58/3.02  tff(c_9556, plain, (v2_struct_0('#skF_6'('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_9268, c_9283, c_8647, c_9265, c_9553])).
% 8.58/3.02  tff(c_9558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8961, c_9556])).
% 8.58/3.02  tff(c_9559, plain, (~l1_struct_0('#skF_6'('#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_9548])).
% 8.58/3.02  tff(c_9602, plain, (~l1_pre_topc('#skF_6'('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_36, c_9559])).
% 8.58/3.02  tff(c_9606, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9268, c_9602])).
% 8.58/3.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.58/3.02  
% 8.58/3.02  Inference rules
% 8.58/3.02  ----------------------
% 8.58/3.02  #Ref     : 0
% 8.58/3.02  #Sup     : 2044
% 8.58/3.02  #Fact    : 2
% 8.58/3.03  #Define  : 0
% 8.58/3.03  #Split   : 15
% 8.58/3.03  #Chain   : 0
% 8.58/3.03  #Close   : 0
% 8.58/3.03  
% 8.58/3.03  Ordering : KBO
% 8.58/3.03  
% 8.58/3.03  Simplification rules
% 8.58/3.03  ----------------------
% 8.58/3.03  #Subsume      : 448
% 8.58/3.03  #Demod        : 966
% 8.58/3.03  #Tautology    : 551
% 8.58/3.03  #SimpNegUnit  : 579
% 8.58/3.03  #BackRed      : 2
% 8.58/3.03  
% 8.58/3.03  #Partial instantiations: 0
% 8.58/3.03  #Strategies tried      : 1
% 8.58/3.03  
% 8.58/3.03  Timing (in seconds)
% 8.58/3.03  ----------------------
% 8.58/3.03  Preprocessing        : 0.48
% 8.58/3.03  Parsing              : 0.24
% 8.58/3.03  CNF conversion       : 0.04
% 8.58/3.03  Main loop            : 1.76
% 8.58/3.03  Inferencing          : 0.54
% 8.58/3.03  Reduction            : 0.55
% 8.58/3.03  Demodulation         : 0.36
% 8.58/3.03  BG Simplification    : 0.07
% 8.58/3.03  Subsumption          : 0.45
% 8.58/3.03  Abstraction          : 0.11
% 8.58/3.03  MUC search           : 0.00
% 8.58/3.03  Cooper               : 0.00
% 8.58/3.03  Total                : 2.30
% 8.58/3.03  Index Insertion      : 0.00
% 8.58/3.03  Index Deletion       : 0.00
% 8.58/3.03  Index Matching       : 0.00
% 8.58/3.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
