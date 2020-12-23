%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:22 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 313 expanded)
%              Number of leaves         :   45 ( 127 expanded)
%              Depth                    :   12
%              Number of atoms          :  179 ( 913 expanded)
%              Number of equality atoms :   12 ( 117 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_6 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_164,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_136,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tops_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_119,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_30,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_32,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_74,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_96,plain,(
    ! [A_1] : r1_tarski('#skF_8',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_82,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_80,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_97,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2])).

tff(c_18,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_1'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_93,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_1'(A_11),A_11)
      | A_11 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_18])).

tff(c_62,plain,(
    ! [A_51] :
      ( l1_struct_0(A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_114,plain,(
    ! [A_71] :
      ( u1_struct_0(A_71) = k2_struct_0(A_71)
      | ~ l1_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_125,plain,(
    ! [A_75] :
      ( u1_struct_0(A_75) = k2_struct_0(A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_62,c_114])).

tff(c_129,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_125])).

tff(c_237,plain,(
    ! [A_97] :
      ( m1_subset_1('#skF_5'(A_97),k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_242,plain,
    ( m1_subset_1('#skF_5'('#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_237])).

tff(c_245,plain,
    ( m1_subset_1('#skF_5'('#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_6')))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_242])).

tff(c_246,plain,(
    m1_subset_1('#skF_5'('#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_245])).

tff(c_12,plain,(
    ! [C_8,B_7,A_6] :
      ( ~ v1_xboole_0(C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_259,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
      | ~ r2_hidden(A_6,'#skF_5'('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_246,c_12])).

tff(c_262,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_259])).

tff(c_78,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_136,plain,(
    m1_subset_1('#skF_7',k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_78])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,(
    ! [A_52] :
      ( v4_pre_topc(k2_struct_0(A_52),A_52)
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_168,plain,(
    ! [A_83] :
      ( r2_hidden(u1_struct_0(A_83),u1_pre_topc(A_83))
      | ~ v2_pre_topc(A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_174,plain,
    ( r2_hidden(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6'))
    | ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_168])).

tff(c_177,plain,(
    r2_hidden(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_82,c_174])).

tff(c_6,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k2_subset_1(A_3),k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_95,plain,(
    ! [A_3] : m1_subset_1(A_3,k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_336,plain,(
    ! [B_105,A_106] :
      ( v3_pre_topc(B_105,A_106)
      | ~ r2_hidden(B_105,u1_pre_topc(A_106))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_370,plain,(
    ! [A_107] :
      ( v3_pre_topc(u1_struct_0(A_107),A_107)
      | ~ r2_hidden(u1_struct_0(A_107),u1_pre_topc(A_107))
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_95,c_336])).

tff(c_379,plain,
    ( v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6')
    | ~ r2_hidden(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6'))
    | ~ l1_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_370])).

tff(c_386,plain,(
    v3_pre_topc(k2_struct_0('#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_177,c_129,c_379])).

tff(c_92,plain,(
    ! [D_66] :
      ( v3_pre_topc(D_66,'#skF_6')
      | ~ r2_hidden(D_66,'#skF_8')
      | ~ m1_subset_1(D_66,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_149,plain,(
    ! [D_79] :
      ( v3_pre_topc(D_79,'#skF_6')
      | ~ r2_hidden(D_79,'#skF_8')
      | ~ m1_subset_1(D_79,k1_zfmisc_1(k2_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_92])).

tff(c_154,plain,
    ( v3_pre_topc(k2_struct_0('#skF_6'),'#skF_6')
    | ~ r2_hidden(k2_struct_0('#skF_6'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_95,c_149])).

tff(c_162,plain,(
    ~ r2_hidden(k2_struct_0('#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_86,plain,(
    ! [D_66] :
      ( r2_hidden(D_66,'#skF_8')
      | ~ r2_hidden('#skF_7',D_66)
      | ~ v4_pre_topc(D_66,'#skF_6')
      | ~ v3_pre_topc(D_66,'#skF_6')
      | ~ m1_subset_1(D_66,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_285,plain,(
    ! [D_100] :
      ( r2_hidden(D_100,'#skF_8')
      | ~ r2_hidden('#skF_7',D_100)
      | ~ v4_pre_topc(D_100,'#skF_6')
      | ~ v3_pre_topc(D_100,'#skF_6')
      | ~ m1_subset_1(D_100,k1_zfmisc_1(k2_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_86])).

tff(c_292,plain,
    ( r2_hidden(k2_struct_0('#skF_6'),'#skF_8')
    | ~ r2_hidden('#skF_7',k2_struct_0('#skF_6'))
    | ~ v4_pre_topc(k2_struct_0('#skF_6'),'#skF_6')
    | ~ v3_pre_topc(k2_struct_0('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_95,c_285])).

tff(c_298,plain,
    ( ~ r2_hidden('#skF_7',k2_struct_0('#skF_6'))
    | ~ v4_pre_topc(k2_struct_0('#skF_6'),'#skF_6')
    | ~ v3_pre_topc(k2_struct_0('#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_292])).

tff(c_431,plain,
    ( ~ r2_hidden('#skF_7',k2_struct_0('#skF_6'))
    | ~ v4_pre_topc(k2_struct_0('#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_298])).

tff(c_432,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_431])).

tff(c_435,plain,
    ( ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_432])).

tff(c_439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_435])).

tff(c_440,plain,(
    ~ r2_hidden('#skF_7',k2_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_431])).

tff(c_447,plain,
    ( v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',k2_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_10,c_440])).

tff(c_450,plain,(
    v1_xboole_0(k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_447])).

tff(c_452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_262,c_450])).

tff(c_531,plain,(
    ! [A_114] : ~ r2_hidden(A_114,'#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_541,plain,(
    '#skF_5'('#skF_6') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_93,c_531])).

tff(c_70,plain,(
    ! [A_53] :
      ( ~ v1_xboole_0('#skF_5'(A_53))
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_555,plain,
    ( ~ v1_xboole_0('#skF_8')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_70])).

tff(c_568,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_97,c_555])).

tff(c_570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_568])).

tff(c_572,plain,(
    r2_hidden(k2_struct_0('#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( ~ r1_tarski(B_10,A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_575,plain,(
    ~ r1_tarski('#skF_8',k2_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_572,c_14])).

tff(c_579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_575])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:51:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.34  
% 2.87/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.35  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_6 > #skF_8 > #skF_3
% 2.87/1.35  
% 2.87/1.35  %Foreground sorts:
% 2.87/1.35  
% 2.87/1.35  
% 2.87/1.35  %Background operators:
% 2.87/1.35  
% 2.87/1.35  
% 2.87/1.35  %Foreground operators:
% 2.87/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.87/1.35  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.87/1.35  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.87/1.35  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.87/1.35  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.87/1.35  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.87/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.87/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.87/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.87/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.87/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.87/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.87/1.35  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.87/1.35  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.87/1.35  tff('#skF_8', type, '#skF_8': $i).
% 2.87/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.35  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.87/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.87/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.87/1.35  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.87/1.35  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.87/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.87/1.35  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.87/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.35  
% 2.87/1.36  tff(f_164, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.87/1.36  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.87/1.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.87/1.36  tff(f_71, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.87/1.36  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.87/1.36  tff(f_100, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.87/1.36  tff(f_136, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_tops_1)).
% 2.87/1.36  tff(f_45, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.87/1.36  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.87/1.36  tff(f_119, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.87/1.36  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 2.87/1.36  tff(f_30, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.87/1.36  tff(f_32, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.87/1.36  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.87/1.36  tff(f_50, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.87/1.36  tff(c_74, plain, (k1_xboole_0='#skF_8'), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.87/1.36  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.87/1.36  tff(c_96, plain, (![A_1]: (r1_tarski('#skF_8', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4])).
% 2.87/1.36  tff(c_84, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.87/1.36  tff(c_82, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.87/1.36  tff(c_80, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.87/1.36  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.87/1.36  tff(c_97, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2])).
% 2.87/1.36  tff(c_18, plain, (![A_11]: (r2_hidden('#skF_1'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.87/1.36  tff(c_93, plain, (![A_11]: (r2_hidden('#skF_1'(A_11), A_11) | A_11='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_18])).
% 2.87/1.36  tff(c_62, plain, (![A_51]: (l1_struct_0(A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.87/1.36  tff(c_114, plain, (![A_71]: (u1_struct_0(A_71)=k2_struct_0(A_71) | ~l1_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.87/1.36  tff(c_125, plain, (![A_75]: (u1_struct_0(A_75)=k2_struct_0(A_75) | ~l1_pre_topc(A_75))), inference(resolution, [status(thm)], [c_62, c_114])).
% 2.87/1.36  tff(c_129, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_80, c_125])).
% 2.87/1.36  tff(c_237, plain, (![A_97]: (m1_subset_1('#skF_5'(A_97), k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.87/1.36  tff(c_242, plain, (m1_subset_1('#skF_5'('#skF_6'), k1_zfmisc_1(k2_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_129, c_237])).
% 2.87/1.36  tff(c_245, plain, (m1_subset_1('#skF_5'('#skF_6'), k1_zfmisc_1(k2_struct_0('#skF_6'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_242])).
% 2.87/1.36  tff(c_246, plain, (m1_subset_1('#skF_5'('#skF_6'), k1_zfmisc_1(k2_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_84, c_245])).
% 2.87/1.36  tff(c_12, plain, (![C_8, B_7, A_6]: (~v1_xboole_0(C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.87/1.36  tff(c_259, plain, (![A_6]: (~v1_xboole_0(k2_struct_0('#skF_6')) | ~r2_hidden(A_6, '#skF_5'('#skF_6')))), inference(resolution, [status(thm)], [c_246, c_12])).
% 2.87/1.36  tff(c_262, plain, (~v1_xboole_0(k2_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_259])).
% 2.87/1.36  tff(c_78, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.87/1.36  tff(c_136, plain, (m1_subset_1('#skF_7', k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_78])).
% 2.87/1.36  tff(c_10, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.87/1.36  tff(c_64, plain, (![A_52]: (v4_pre_topc(k2_struct_0(A_52), A_52) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.87/1.36  tff(c_168, plain, (![A_83]: (r2_hidden(u1_struct_0(A_83), u1_pre_topc(A_83)) | ~v2_pre_topc(A_83) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.87/1.36  tff(c_174, plain, (r2_hidden(k2_struct_0('#skF_6'), u1_pre_topc('#skF_6')) | ~v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_129, c_168])).
% 2.87/1.36  tff(c_177, plain, (r2_hidden(k2_struct_0('#skF_6'), u1_pre_topc('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_82, c_174])).
% 2.87/1.37  tff(c_6, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.87/1.37  tff(c_8, plain, (![A_3]: (m1_subset_1(k2_subset_1(A_3), k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.87/1.37  tff(c_95, plain, (![A_3]: (m1_subset_1(A_3, k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.87/1.37  tff(c_336, plain, (![B_105, A_106]: (v3_pre_topc(B_105, A_106) | ~r2_hidden(B_105, u1_pre_topc(A_106)) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.87/1.37  tff(c_370, plain, (![A_107]: (v3_pre_topc(u1_struct_0(A_107), A_107) | ~r2_hidden(u1_struct_0(A_107), u1_pre_topc(A_107)) | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_95, c_336])).
% 2.87/1.37  tff(c_379, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6') | ~r2_hidden(k2_struct_0('#skF_6'), u1_pre_topc('#skF_6')) | ~l1_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_129, c_370])).
% 2.87/1.37  tff(c_386, plain, (v3_pre_topc(k2_struct_0('#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_177, c_129, c_379])).
% 2.87/1.37  tff(c_92, plain, (![D_66]: (v3_pre_topc(D_66, '#skF_6') | ~r2_hidden(D_66, '#skF_8') | ~m1_subset_1(D_66, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.87/1.37  tff(c_149, plain, (![D_79]: (v3_pre_topc(D_79, '#skF_6') | ~r2_hidden(D_79, '#skF_8') | ~m1_subset_1(D_79, k1_zfmisc_1(k2_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_92])).
% 2.87/1.37  tff(c_154, plain, (v3_pre_topc(k2_struct_0('#skF_6'), '#skF_6') | ~r2_hidden(k2_struct_0('#skF_6'), '#skF_8')), inference(resolution, [status(thm)], [c_95, c_149])).
% 2.87/1.37  tff(c_162, plain, (~r2_hidden(k2_struct_0('#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_154])).
% 2.87/1.37  tff(c_86, plain, (![D_66]: (r2_hidden(D_66, '#skF_8') | ~r2_hidden('#skF_7', D_66) | ~v4_pre_topc(D_66, '#skF_6') | ~v3_pre_topc(D_66, '#skF_6') | ~m1_subset_1(D_66, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.87/1.37  tff(c_285, plain, (![D_100]: (r2_hidden(D_100, '#skF_8') | ~r2_hidden('#skF_7', D_100) | ~v4_pre_topc(D_100, '#skF_6') | ~v3_pre_topc(D_100, '#skF_6') | ~m1_subset_1(D_100, k1_zfmisc_1(k2_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_86])).
% 2.87/1.37  tff(c_292, plain, (r2_hidden(k2_struct_0('#skF_6'), '#skF_8') | ~r2_hidden('#skF_7', k2_struct_0('#skF_6')) | ~v4_pre_topc(k2_struct_0('#skF_6'), '#skF_6') | ~v3_pre_topc(k2_struct_0('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_95, c_285])).
% 2.87/1.37  tff(c_298, plain, (~r2_hidden('#skF_7', k2_struct_0('#skF_6')) | ~v4_pre_topc(k2_struct_0('#skF_6'), '#skF_6') | ~v3_pre_topc(k2_struct_0('#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_162, c_292])).
% 2.87/1.37  tff(c_431, plain, (~r2_hidden('#skF_7', k2_struct_0('#skF_6')) | ~v4_pre_topc(k2_struct_0('#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_386, c_298])).
% 2.87/1.37  tff(c_432, plain, (~v4_pre_topc(k2_struct_0('#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_431])).
% 2.87/1.37  tff(c_435, plain, (~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_64, c_432])).
% 2.87/1.37  tff(c_439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_435])).
% 2.87/1.37  tff(c_440, plain, (~r2_hidden('#skF_7', k2_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_431])).
% 2.87/1.37  tff(c_447, plain, (v1_xboole_0(k2_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', k2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_10, c_440])).
% 2.87/1.37  tff(c_450, plain, (v1_xboole_0(k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_447])).
% 2.87/1.37  tff(c_452, plain, $false, inference(negUnitSimplification, [status(thm)], [c_262, c_450])).
% 2.87/1.37  tff(c_531, plain, (![A_114]: (~r2_hidden(A_114, '#skF_5'('#skF_6')))), inference(splitRight, [status(thm)], [c_259])).
% 2.87/1.37  tff(c_541, plain, ('#skF_5'('#skF_6')='#skF_8'), inference(resolution, [status(thm)], [c_93, c_531])).
% 2.87/1.37  tff(c_70, plain, (![A_53]: (~v1_xboole_0('#skF_5'(A_53)) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.87/1.37  tff(c_555, plain, (~v1_xboole_0('#skF_8') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_541, c_70])).
% 2.87/1.37  tff(c_568, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_97, c_555])).
% 2.87/1.37  tff(c_570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_568])).
% 2.87/1.37  tff(c_572, plain, (r2_hidden(k2_struct_0('#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_154])).
% 2.87/1.37  tff(c_14, plain, (![B_10, A_9]: (~r1_tarski(B_10, A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.87/1.37  tff(c_575, plain, (~r1_tarski('#skF_8', k2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_572, c_14])).
% 2.87/1.37  tff(c_579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_575])).
% 2.87/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.37  
% 2.87/1.37  Inference rules
% 2.87/1.37  ----------------------
% 2.87/1.37  #Ref     : 0
% 2.87/1.37  #Sup     : 89
% 2.87/1.37  #Fact    : 0
% 2.87/1.37  #Define  : 0
% 2.87/1.37  #Split   : 7
% 2.87/1.37  #Chain   : 0
% 2.87/1.37  #Close   : 0
% 2.87/1.37  
% 2.87/1.37  Ordering : KBO
% 2.87/1.37  
% 2.87/1.37  Simplification rules
% 2.87/1.37  ----------------------
% 2.87/1.37  #Subsume      : 10
% 2.87/1.37  #Demod        : 88
% 2.87/1.37  #Tautology    : 29
% 2.87/1.37  #SimpNegUnit  : 11
% 2.87/1.37  #BackRed      : 15
% 2.87/1.37  
% 2.87/1.37  #Partial instantiations: 0
% 2.87/1.37  #Strategies tried      : 1
% 2.87/1.37  
% 2.87/1.37  Timing (in seconds)
% 2.87/1.37  ----------------------
% 2.87/1.37  Preprocessing        : 0.34
% 2.87/1.37  Parsing              : 0.18
% 2.87/1.37  CNF conversion       : 0.03
% 2.87/1.37  Main loop            : 0.29
% 2.87/1.37  Inferencing          : 0.10
% 2.87/1.37  Reduction            : 0.10
% 2.87/1.37  Demodulation         : 0.07
% 2.87/1.37  BG Simplification    : 0.02
% 2.87/1.37  Subsumption          : 0.05
% 2.87/1.37  Abstraction          : 0.01
% 2.87/1.37  MUC search           : 0.00
% 2.87/1.37  Cooper               : 0.00
% 2.87/1.37  Total                : 0.67
% 2.87/1.37  Index Insertion      : 0.00
% 2.87/1.37  Index Deletion       : 0.00
% 2.87/1.37  Index Matching       : 0.00
% 2.87/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
