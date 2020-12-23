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
% DateTime   : Thu Dec  3 10:26:36 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 244 expanded)
%              Number of leaves         :   30 (  88 expanded)
%              Depth                    :   16
%              Number of atoms          :  215 ( 893 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( m1_pre_topc(B,C)
                     => ( ( r1_tsep_1(B,D)
                          & r1_tsep_1(D,B) )
                        | ( ~ r1_tsep_1(C,D)
                          & ~ r1_tsep_1(D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_36,plain,(
    m1_pre_topc('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_547,plain,(
    ! [B_143,A_144] :
      ( l1_pre_topc(B_143)
      | ~ m1_pre_topc(B_143,A_144)
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_550,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_547])).

tff(c_562,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_550])).

tff(c_18,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_553,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_547])).

tff(c_565,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_553])).

tff(c_40,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_469,plain,(
    ! [B_120,A_121] :
      ( l1_pre_topc(B_120)
      | ~ m1_pre_topc(B_120,A_121)
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_481,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_469])).

tff(c_491,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_481])).

tff(c_472,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_469])).

tff(c_484,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_472])).

tff(c_56,plain,(
    ! [B_37,A_38] :
      ( l1_pre_topc(B_37)
      | ~ m1_pre_topc(B_37,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_62,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_56])).

tff(c_74,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_62])).

tff(c_34,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_59,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_56])).

tff(c_71,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_59])).

tff(c_68,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_56])).

tff(c_78,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_68])).

tff(c_30,plain,
    ( r1_tsep_1('#skF_6','#skF_5')
    | r1_tsep_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_55,plain,(
    r1_tsep_1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_108,plain,(
    ! [B_58,A_59] :
      ( r1_tsep_1(B_58,A_59)
      | ~ r1_tsep_1(A_59,B_58)
      | ~ l1_struct_0(B_58)
      | ~ l1_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_111,plain,
    ( r1_tsep_1('#skF_6','#skF_5')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_55,c_108])).

tff(c_112,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_115,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_112])).

tff(c_119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_115])).

tff(c_120,plain,
    ( ~ l1_struct_0('#skF_6')
    | r1_tsep_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_122,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_125,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_122])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_125])).

tff(c_131,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_132,plain,(
    ! [B_60,A_61] :
      ( m1_subset_1(u1_struct_0(B_60),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_pre_topc(B_60,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_136,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(u1_struct_0(B_60),u1_struct_0(A_61))
      | ~ m1_pre_topc(B_60,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_132,c_14])).

tff(c_121,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_98,plain,(
    ! [C_55,B_56,A_57] :
      ( r2_hidden(C_55,B_56)
      | ~ r2_hidden(C_55,A_57)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_105,plain,(
    ! [A_6,B_7,B_56] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_56)
      | ~ r1_tarski(B_7,B_56)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_98])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_143,plain,(
    ! [A_64,B_65] :
      ( r1_xboole_0(u1_struct_0(A_64),u1_struct_0(B_65))
      | ~ r1_tsep_1(A_64,B_65)
      | ~ l1_struct_0(B_65)
      | ~ l1_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,B_7)
      | ~ r2_hidden(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_176,plain,(
    ! [C_81,B_82,A_83] :
      ( ~ r2_hidden(C_81,u1_struct_0(B_82))
      | ~ r2_hidden(C_81,u1_struct_0(A_83))
      | ~ r1_tsep_1(A_83,B_82)
      | ~ l1_struct_0(B_82)
      | ~ l1_struct_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_143,c_8])).

tff(c_215,plain,(
    ! [B_92,B_93,A_94] :
      ( ~ r2_hidden('#skF_2'(u1_struct_0(B_92),B_93),u1_struct_0(A_94))
      | ~ r1_tsep_1(A_94,B_92)
      | ~ l1_struct_0(B_92)
      | ~ l1_struct_0(A_94)
      | r1_xboole_0(u1_struct_0(B_92),B_93) ) ),
    inference(resolution,[status(thm)],[c_12,c_176])).

tff(c_245,plain,(
    ! [A_99,B_100,B_101] :
      ( ~ r1_tsep_1(A_99,B_100)
      | ~ l1_struct_0(B_100)
      | ~ l1_struct_0(A_99)
      | ~ r1_tarski(B_101,u1_struct_0(A_99))
      | r1_xboole_0(u1_struct_0(B_100),B_101) ) ),
    inference(resolution,[status(thm)],[c_105,c_215])).

tff(c_249,plain,(
    ! [B_101] :
      ( ~ l1_struct_0('#skF_6')
      | ~ l1_struct_0('#skF_5')
      | ~ r1_tarski(B_101,u1_struct_0('#skF_5'))
      | r1_xboole_0(u1_struct_0('#skF_6'),B_101) ) ),
    inference(resolution,[status(thm)],[c_55,c_245])).

tff(c_267,plain,(
    ! [B_103] :
      ( ~ r1_tarski(B_103,u1_struct_0('#skF_5'))
      | r1_xboole_0(u1_struct_0('#skF_6'),B_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_131,c_249])).

tff(c_22,plain,(
    ! [A_17,B_19] :
      ( r1_tsep_1(A_17,B_19)
      | ~ r1_xboole_0(u1_struct_0(A_17),u1_struct_0(B_19))
      | ~ l1_struct_0(B_19)
      | ~ l1_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_271,plain,(
    ! [B_19] :
      ( r1_tsep_1('#skF_6',B_19)
      | ~ l1_struct_0(B_19)
      | ~ l1_struct_0('#skF_6')
      | ~ r1_tarski(u1_struct_0(B_19),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_267,c_22])).

tff(c_371,plain,(
    ! [B_114] :
      ( r1_tsep_1('#skF_6',B_114)
      | ~ l1_struct_0(B_114)
      | ~ r1_tarski(u1_struct_0(B_114),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_271])).

tff(c_375,plain,(
    ! [B_60] :
      ( r1_tsep_1('#skF_6',B_60)
      | ~ l1_struct_0(B_60)
      | ~ m1_pre_topc(B_60,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_136,c_371])).

tff(c_386,plain,(
    ! [B_115] :
      ( r1_tsep_1('#skF_6',B_115)
      | ~ l1_struct_0(B_115)
      | ~ m1_pre_topc(B_115,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_375])).

tff(c_26,plain,(
    ! [B_21,A_20] :
      ( r1_tsep_1(B_21,A_20)
      | ~ r1_tsep_1(A_20,B_21)
      | ~ l1_struct_0(B_21)
      | ~ l1_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_396,plain,(
    ! [B_115] :
      ( r1_tsep_1(B_115,'#skF_6')
      | ~ l1_struct_0('#skF_6')
      | ~ l1_struct_0(B_115)
      | ~ m1_pre_topc(B_115,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_386,c_26])).

tff(c_431,plain,(
    ! [B_119] :
      ( r1_tsep_1(B_119,'#skF_6')
      | ~ l1_struct_0(B_119)
      | ~ m1_pre_topc(B_119,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_396])).

tff(c_32,plain,
    ( ~ r1_tsep_1('#skF_6','#skF_4')
    | ~ r1_tsep_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_54,plain,(
    ~ r1_tsep_1('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_444,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_431,c_54])).

tff(c_459,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_444])).

tff(c_462,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_459])).

tff(c_466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_462])).

tff(c_468,plain,(
    ~ r1_tsep_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_467,plain,(
    r1_tsep_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_521,plain,(
    ! [B_141,A_142] :
      ( r1_tsep_1(B_141,A_142)
      | ~ r1_tsep_1(A_142,B_141)
      | ~ l1_struct_0(B_141)
      | ~ l1_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_523,plain,
    ( r1_tsep_1('#skF_5','#skF_6')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_467,c_521])).

tff(c_526,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_468,c_523])).

tff(c_527,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_526])).

tff(c_530,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_527])).

tff(c_534,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_530])).

tff(c_535,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_526])).

tff(c_539,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_535])).

tff(c_543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_539])).

tff(c_544,plain,(
    ~ r1_tsep_1('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_545,plain,(
    r1_tsep_1('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_599,plain,(
    ! [B_164,A_165] :
      ( r1_tsep_1(B_164,A_165)
      | ~ r1_tsep_1(A_165,B_164)
      | ~ l1_struct_0(B_164)
      | ~ l1_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_603,plain,
    ( r1_tsep_1('#skF_6','#skF_4')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_545,c_599])).

tff(c_607,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_544,c_603])).

tff(c_608,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_607])).

tff(c_611,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_608])).

tff(c_615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_611])).

tff(c_616,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_607])).

tff(c_620,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_616])).

tff(c_624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_620])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:10:19 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.40  
% 2.80/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.40  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.80/1.40  
% 2.80/1.40  %Foreground sorts:
% 2.80/1.40  
% 2.80/1.40  
% 2.80/1.40  %Background operators:
% 2.80/1.40  
% 2.80/1.40  
% 2.80/1.40  %Foreground operators:
% 2.80/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.80/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.80/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.80/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.80/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.80/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.80/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.80/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.80/1.40  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.80/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.80/1.40  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.80/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.80/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.80/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.40  
% 2.80/1.42  tff(f_127, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 2.80/1.42  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.80/1.42  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.80/1.42  tff(f_82, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.80/1.42  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.80/1.42  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.80/1.42  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.80/1.42  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.80/1.42  tff(f_74, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.80/1.42  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.80/1.42  tff(c_36, plain, (m1_pre_topc('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.80/1.42  tff(c_547, plain, (![B_143, A_144]: (l1_pre_topc(B_143) | ~m1_pre_topc(B_143, A_144) | ~l1_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.80/1.42  tff(c_550, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_547])).
% 2.80/1.42  tff(c_562, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_550])).
% 2.80/1.42  tff(c_18, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.80/1.42  tff(c_44, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.80/1.42  tff(c_553, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_547])).
% 2.80/1.42  tff(c_565, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_553])).
% 2.80/1.42  tff(c_40, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.80/1.42  tff(c_469, plain, (![B_120, A_121]: (l1_pre_topc(B_120) | ~m1_pre_topc(B_120, A_121) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.80/1.42  tff(c_481, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_469])).
% 2.80/1.42  tff(c_491, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_481])).
% 2.80/1.42  tff(c_472, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_469])).
% 2.80/1.42  tff(c_484, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_472])).
% 2.80/1.42  tff(c_56, plain, (![B_37, A_38]: (l1_pre_topc(B_37) | ~m1_pre_topc(B_37, A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.80/1.42  tff(c_62, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_56])).
% 2.80/1.42  tff(c_74, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_62])).
% 2.80/1.42  tff(c_34, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.80/1.42  tff(c_59, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_56])).
% 2.80/1.42  tff(c_71, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_59])).
% 2.80/1.42  tff(c_68, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_56])).
% 2.80/1.42  tff(c_78, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_68])).
% 2.80/1.42  tff(c_30, plain, (r1_tsep_1('#skF_6', '#skF_5') | r1_tsep_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.80/1.42  tff(c_55, plain, (r1_tsep_1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_30])).
% 2.80/1.42  tff(c_108, plain, (![B_58, A_59]: (r1_tsep_1(B_58, A_59) | ~r1_tsep_1(A_59, B_58) | ~l1_struct_0(B_58) | ~l1_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.80/1.42  tff(c_111, plain, (r1_tsep_1('#skF_6', '#skF_5') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_55, c_108])).
% 2.80/1.42  tff(c_112, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_111])).
% 2.80/1.42  tff(c_115, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_18, c_112])).
% 2.80/1.42  tff(c_119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_115])).
% 2.80/1.42  tff(c_120, plain, (~l1_struct_0('#skF_6') | r1_tsep_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_111])).
% 2.80/1.42  tff(c_122, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_120])).
% 2.80/1.42  tff(c_125, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_18, c_122])).
% 2.80/1.42  tff(c_129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_125])).
% 2.80/1.42  tff(c_131, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_120])).
% 2.80/1.42  tff(c_132, plain, (![B_60, A_61]: (m1_subset_1(u1_struct_0(B_60), k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_pre_topc(B_60, A_61) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.80/1.42  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.80/1.42  tff(c_136, plain, (![B_60, A_61]: (r1_tarski(u1_struct_0(B_60), u1_struct_0(A_61)) | ~m1_pre_topc(B_60, A_61) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_132, c_14])).
% 2.80/1.42  tff(c_121, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_111])).
% 2.80/1.42  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.80/1.42  tff(c_98, plain, (![C_55, B_56, A_57]: (r2_hidden(C_55, B_56) | ~r2_hidden(C_55, A_57) | ~r1_tarski(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.80/1.42  tff(c_105, plain, (![A_6, B_7, B_56]: (r2_hidden('#skF_2'(A_6, B_7), B_56) | ~r1_tarski(B_7, B_56) | r1_xboole_0(A_6, B_7))), inference(resolution, [status(thm)], [c_10, c_98])).
% 2.80/1.42  tff(c_12, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.80/1.42  tff(c_143, plain, (![A_64, B_65]: (r1_xboole_0(u1_struct_0(A_64), u1_struct_0(B_65)) | ~r1_tsep_1(A_64, B_65) | ~l1_struct_0(B_65) | ~l1_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.80/1.42  tff(c_8, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, B_7) | ~r2_hidden(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.80/1.42  tff(c_176, plain, (![C_81, B_82, A_83]: (~r2_hidden(C_81, u1_struct_0(B_82)) | ~r2_hidden(C_81, u1_struct_0(A_83)) | ~r1_tsep_1(A_83, B_82) | ~l1_struct_0(B_82) | ~l1_struct_0(A_83))), inference(resolution, [status(thm)], [c_143, c_8])).
% 2.80/1.42  tff(c_215, plain, (![B_92, B_93, A_94]: (~r2_hidden('#skF_2'(u1_struct_0(B_92), B_93), u1_struct_0(A_94)) | ~r1_tsep_1(A_94, B_92) | ~l1_struct_0(B_92) | ~l1_struct_0(A_94) | r1_xboole_0(u1_struct_0(B_92), B_93))), inference(resolution, [status(thm)], [c_12, c_176])).
% 2.80/1.42  tff(c_245, plain, (![A_99, B_100, B_101]: (~r1_tsep_1(A_99, B_100) | ~l1_struct_0(B_100) | ~l1_struct_0(A_99) | ~r1_tarski(B_101, u1_struct_0(A_99)) | r1_xboole_0(u1_struct_0(B_100), B_101))), inference(resolution, [status(thm)], [c_105, c_215])).
% 2.80/1.42  tff(c_249, plain, (![B_101]: (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | ~r1_tarski(B_101, u1_struct_0('#skF_5')) | r1_xboole_0(u1_struct_0('#skF_6'), B_101))), inference(resolution, [status(thm)], [c_55, c_245])).
% 2.80/1.42  tff(c_267, plain, (![B_103]: (~r1_tarski(B_103, u1_struct_0('#skF_5')) | r1_xboole_0(u1_struct_0('#skF_6'), B_103))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_131, c_249])).
% 2.80/1.42  tff(c_22, plain, (![A_17, B_19]: (r1_tsep_1(A_17, B_19) | ~r1_xboole_0(u1_struct_0(A_17), u1_struct_0(B_19)) | ~l1_struct_0(B_19) | ~l1_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.80/1.42  tff(c_271, plain, (![B_19]: (r1_tsep_1('#skF_6', B_19) | ~l1_struct_0(B_19) | ~l1_struct_0('#skF_6') | ~r1_tarski(u1_struct_0(B_19), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_267, c_22])).
% 2.80/1.42  tff(c_371, plain, (![B_114]: (r1_tsep_1('#skF_6', B_114) | ~l1_struct_0(B_114) | ~r1_tarski(u1_struct_0(B_114), u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_271])).
% 2.80/1.42  tff(c_375, plain, (![B_60]: (r1_tsep_1('#skF_6', B_60) | ~l1_struct_0(B_60) | ~m1_pre_topc(B_60, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_136, c_371])).
% 2.80/1.42  tff(c_386, plain, (![B_115]: (r1_tsep_1('#skF_6', B_115) | ~l1_struct_0(B_115) | ~m1_pre_topc(B_115, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_375])).
% 2.80/1.42  tff(c_26, plain, (![B_21, A_20]: (r1_tsep_1(B_21, A_20) | ~r1_tsep_1(A_20, B_21) | ~l1_struct_0(B_21) | ~l1_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.80/1.42  tff(c_396, plain, (![B_115]: (r1_tsep_1(B_115, '#skF_6') | ~l1_struct_0('#skF_6') | ~l1_struct_0(B_115) | ~m1_pre_topc(B_115, '#skF_5'))), inference(resolution, [status(thm)], [c_386, c_26])).
% 2.80/1.42  tff(c_431, plain, (![B_119]: (r1_tsep_1(B_119, '#skF_6') | ~l1_struct_0(B_119) | ~m1_pre_topc(B_119, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_396])).
% 2.80/1.42  tff(c_32, plain, (~r1_tsep_1('#skF_6', '#skF_4') | ~r1_tsep_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.80/1.42  tff(c_54, plain, (~r1_tsep_1('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_32])).
% 2.80/1.42  tff(c_444, plain, (~l1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_431, c_54])).
% 2.80/1.42  tff(c_459, plain, (~l1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_444])).
% 2.80/1.42  tff(c_462, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_18, c_459])).
% 2.80/1.42  tff(c_466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_462])).
% 2.80/1.42  tff(c_468, plain, (~r1_tsep_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_30])).
% 2.80/1.42  tff(c_467, plain, (r1_tsep_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_30])).
% 2.80/1.42  tff(c_521, plain, (![B_141, A_142]: (r1_tsep_1(B_141, A_142) | ~r1_tsep_1(A_142, B_141) | ~l1_struct_0(B_141) | ~l1_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.80/1.42  tff(c_523, plain, (r1_tsep_1('#skF_5', '#skF_6') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_467, c_521])).
% 2.80/1.42  tff(c_526, plain, (~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_468, c_523])).
% 2.80/1.42  tff(c_527, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_526])).
% 2.80/1.42  tff(c_530, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_18, c_527])).
% 2.80/1.42  tff(c_534, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_484, c_530])).
% 2.80/1.42  tff(c_535, plain, (~l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_526])).
% 2.80/1.42  tff(c_539, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_18, c_535])).
% 2.80/1.42  tff(c_543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_491, c_539])).
% 2.80/1.42  tff(c_544, plain, (~r1_tsep_1('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_32])).
% 2.80/1.42  tff(c_545, plain, (r1_tsep_1('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_32])).
% 2.80/1.42  tff(c_599, plain, (![B_164, A_165]: (r1_tsep_1(B_164, A_165) | ~r1_tsep_1(A_165, B_164) | ~l1_struct_0(B_164) | ~l1_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.80/1.42  tff(c_603, plain, (r1_tsep_1('#skF_6', '#skF_4') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_545, c_599])).
% 2.80/1.42  tff(c_607, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_544, c_603])).
% 2.80/1.42  tff(c_608, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_607])).
% 2.80/1.42  tff(c_611, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_18, c_608])).
% 2.80/1.42  tff(c_615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_565, c_611])).
% 2.80/1.42  tff(c_616, plain, (~l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_607])).
% 2.80/1.42  tff(c_620, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_18, c_616])).
% 2.80/1.42  tff(c_624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_562, c_620])).
% 2.80/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.42  
% 2.80/1.42  Inference rules
% 2.80/1.42  ----------------------
% 2.80/1.42  #Ref     : 0
% 2.80/1.42  #Sup     : 103
% 2.80/1.42  #Fact    : 0
% 2.80/1.42  #Define  : 0
% 2.80/1.42  #Split   : 9
% 2.80/1.42  #Chain   : 0
% 2.80/1.42  #Close   : 0
% 2.80/1.42  
% 2.80/1.42  Ordering : KBO
% 2.80/1.42  
% 2.80/1.42  Simplification rules
% 2.80/1.42  ----------------------
% 2.80/1.42  #Subsume      : 13
% 2.80/1.42  #Demod        : 54
% 2.80/1.42  #Tautology    : 11
% 2.80/1.42  #SimpNegUnit  : 2
% 2.80/1.42  #BackRed      : 0
% 2.80/1.42  
% 2.80/1.42  #Partial instantiations: 0
% 2.80/1.42  #Strategies tried      : 1
% 2.80/1.42  
% 2.80/1.42  Timing (in seconds)
% 2.80/1.42  ----------------------
% 2.80/1.42  Preprocessing        : 0.30
% 2.80/1.42  Parsing              : 0.17
% 2.80/1.42  CNF conversion       : 0.02
% 2.80/1.42  Main loop            : 0.33
% 2.80/1.42  Inferencing          : 0.13
% 2.80/1.42  Reduction            : 0.08
% 2.80/1.42  Demodulation         : 0.06
% 2.80/1.42  BG Simplification    : 0.02
% 2.80/1.42  Subsumption          : 0.07
% 2.80/1.42  Abstraction          : 0.01
% 2.80/1.42  MUC search           : 0.00
% 2.80/1.42  Cooper               : 0.00
% 2.80/1.42  Total                : 0.67
% 2.80/1.42  Index Insertion      : 0.00
% 2.80/1.42  Index Deletion       : 0.00
% 2.80/1.42  Index Matching       : 0.00
% 2.80/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
