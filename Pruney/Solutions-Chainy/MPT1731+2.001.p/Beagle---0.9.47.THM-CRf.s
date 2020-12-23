%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:46 EST 2020

% Result     : Theorem 4.32s
% Output     : CNFRefutation 4.61s
% Verified   : 
% Statistics : Number of formulae       :  213 ( 810 expanded)
%              Number of leaves         :   26 ( 263 expanded)
%              Depth                    :   15
%              Number of atoms          :  657 (4988 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_170,negated_conjecture,(
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
                   => ( ( r1_tsep_1(k1_tsep_1(A,B,C),D)
                       => ( r1_tsep_1(B,D)
                          & r1_tsep_1(C,D) ) )
                      & ( ( r1_tsep_1(B,D)
                          & r1_tsep_1(C,D) )
                       => r1_tsep_1(k1_tsep_1(A,B,C),D) )
                      & ( r1_tsep_1(D,k1_tsep_1(A,B,C))
                       => ( r1_tsep_1(D,B)
                          & r1_tsep_1(D,C) ) )
                      & ( ( r1_tsep_1(D,B)
                          & r1_tsep_1(D,C) )
                       => r1_tsep_1(D,k1_tsep_1(A,B,C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tmap_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_120,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_pre_topc(D)
                    & m1_pre_topc(D,A) )
                 => ( D = k1_tsep_1(A,B,C)
                  <=> u1_struct_0(D) = k2_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_28,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_788,plain,(
    ! [B_205,A_206] :
      ( l1_pre_topc(B_205)
      | ~ m1_pre_topc(B_205,A_206)
      | ~ l1_pre_topc(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_794,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_788])).

tff(c_803,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_794])).

tff(c_8,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_791,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_788])).

tff(c_800,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_791])).

tff(c_36,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_119,plain,(
    ! [B_43,A_44] :
      ( l1_pre_topc(B_43)
      | ~ m1_pre_topc(B_43,A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_128,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_119])).

tff(c_137,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_128])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_211,plain,(
    ! [A_66,B_67,C_68] :
      ( m1_pre_topc(k1_tsep_1(A_66,B_67,C_68),A_66)
      | ~ m1_pre_topc(C_68,A_66)
      | v2_struct_0(C_68)
      | ~ m1_pre_topc(B_67,A_66)
      | v2_struct_0(B_67)
      | ~ l1_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_10,plain,(
    ! [B_7,A_5] :
      ( l1_pre_topc(B_7)
      | ~ m1_pre_topc(B_7,A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_215,plain,(
    ! [A_66,B_67,C_68] :
      ( l1_pre_topc(k1_tsep_1(A_66,B_67,C_68))
      | ~ m1_pre_topc(C_68,A_66)
      | v2_struct_0(C_68)
      | ~ m1_pre_topc(B_67,A_66)
      | v2_struct_0(B_67)
      | ~ l1_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_211,c_10])).

tff(c_125,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_119])).

tff(c_134,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_125])).

tff(c_92,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_117,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_140,plain,(
    ! [B_51,A_52] :
      ( r1_tsep_1(B_51,A_52)
      | ~ r1_tsep_1(A_52,B_51)
      | ~ l1_struct_0(B_51)
      | ~ l1_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_143,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_117,c_140])).

tff(c_145,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_148,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_145])).

tff(c_152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_148])).

tff(c_154,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_116,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_186,plain,(
    r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_26,plain,(
    ! [B_30,A_29] :
      ( r1_tsep_1(B_30,A_29)
      | ~ r1_tsep_1(A_29,B_30)
      | ~ l1_struct_0(B_30)
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_188,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_186,c_26])).

tff(c_191,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_188])).

tff(c_192,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_195,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_192])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_195])).

tff(c_201,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_122,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_119])).

tff(c_131,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_122])).

tff(c_153,plain,
    ( ~ l1_struct_0('#skF_3')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_155,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_158,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_155])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_158])).

tff(c_164,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_18,plain,(
    ! [A_23,B_25] :
      ( r1_xboole_0(u1_struct_0(A_23),u1_struct_0(B_25))
      | ~ r1_tsep_1(A_23,B_25)
      | ~ l1_struct_0(B_25)
      | ~ l1_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22,plain,(
    ! [A_26,B_27,C_28] :
      ( v1_pre_topc(k1_tsep_1(A_26,B_27,C_28))
      | ~ m1_pre_topc(C_28,A_26)
      | v2_struct_0(C_28)
      | ~ m1_pre_topc(B_27,A_26)
      | v2_struct_0(B_27)
      | ~ l1_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_20,plain,(
    ! [A_26,B_27,C_28] :
      ( m1_pre_topc(k1_tsep_1(A_26,B_27,C_28),A_26)
      | ~ m1_pre_topc(C_28,A_26)
      | v2_struct_0(C_28)
      | ~ m1_pre_topc(B_27,A_26)
      | v2_struct_0(B_27)
      | ~ l1_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_227,plain,(
    ! [A_76,B_77,C_78] :
      ( u1_struct_0(k1_tsep_1(A_76,B_77,C_78)) = k2_xboole_0(u1_struct_0(B_77),u1_struct_0(C_78))
      | ~ m1_pre_topc(k1_tsep_1(A_76,B_77,C_78),A_76)
      | ~ v1_pre_topc(k1_tsep_1(A_76,B_77,C_78))
      | v2_struct_0(k1_tsep_1(A_76,B_77,C_78))
      | ~ m1_pre_topc(C_78,A_76)
      | v2_struct_0(C_78)
      | ~ m1_pre_topc(B_77,A_76)
      | v2_struct_0(B_77)
      | ~ l1_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_231,plain,(
    ! [A_79,B_80,C_81] :
      ( u1_struct_0(k1_tsep_1(A_79,B_80,C_81)) = k2_xboole_0(u1_struct_0(B_80),u1_struct_0(C_81))
      | ~ v1_pre_topc(k1_tsep_1(A_79,B_80,C_81))
      | v2_struct_0(k1_tsep_1(A_79,B_80,C_81))
      | ~ m1_pre_topc(C_81,A_79)
      | v2_struct_0(C_81)
      | ~ m1_pre_topc(B_80,A_79)
      | v2_struct_0(B_80)
      | ~ l1_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_20,c_227])).

tff(c_24,plain,(
    ! [A_26,B_27,C_28] :
      ( ~ v2_struct_0(k1_tsep_1(A_26,B_27,C_28))
      | ~ m1_pre_topc(C_28,A_26)
      | v2_struct_0(C_28)
      | ~ m1_pre_topc(B_27,A_26)
      | v2_struct_0(B_27)
      | ~ l1_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_291,plain,(
    ! [A_82,B_83,C_84] :
      ( u1_struct_0(k1_tsep_1(A_82,B_83,C_84)) = k2_xboole_0(u1_struct_0(B_83),u1_struct_0(C_84))
      | ~ v1_pre_topc(k1_tsep_1(A_82,B_83,C_84))
      | ~ m1_pre_topc(C_84,A_82)
      | v2_struct_0(C_84)
      | ~ m1_pre_topc(B_83,A_82)
      | v2_struct_0(B_83)
      | ~ l1_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_231,c_24])).

tff(c_295,plain,(
    ! [A_85,B_86,C_87] :
      ( u1_struct_0(k1_tsep_1(A_85,B_86,C_87)) = k2_xboole_0(u1_struct_0(B_86),u1_struct_0(C_87))
      | ~ m1_pre_topc(C_87,A_85)
      | v2_struct_0(C_87)
      | ~ m1_pre_topc(B_86,A_85)
      | v2_struct_0(B_86)
      | ~ l1_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_22,c_291])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( ~ r1_xboole_0(A_1,C_3)
      | ~ r1_xboole_0(A_1,B_2)
      | r1_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_369,plain,(
    ! [A_96,C_97,B_98,A_99] :
      ( ~ r1_xboole_0(A_96,u1_struct_0(C_97))
      | ~ r1_xboole_0(A_96,u1_struct_0(B_98))
      | r1_xboole_0(A_96,u1_struct_0(k1_tsep_1(A_99,B_98,C_97)))
      | ~ m1_pre_topc(C_97,A_99)
      | v2_struct_0(C_97)
      | ~ m1_pre_topc(B_98,A_99)
      | v2_struct_0(B_98)
      | ~ l1_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_2])).

tff(c_16,plain,(
    ! [A_23,B_25] :
      ( r1_tsep_1(A_23,B_25)
      | ~ r1_xboole_0(u1_struct_0(A_23),u1_struct_0(B_25))
      | ~ l1_struct_0(B_25)
      | ~ l1_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_416,plain,(
    ! [A_124,A_125,B_126,C_127] :
      ( r1_tsep_1(A_124,k1_tsep_1(A_125,B_126,C_127))
      | ~ l1_struct_0(k1_tsep_1(A_125,B_126,C_127))
      | ~ l1_struct_0(A_124)
      | ~ r1_xboole_0(u1_struct_0(A_124),u1_struct_0(C_127))
      | ~ r1_xboole_0(u1_struct_0(A_124),u1_struct_0(B_126))
      | ~ m1_pre_topc(C_127,A_125)
      | v2_struct_0(C_127)
      | ~ m1_pre_topc(B_126,A_125)
      | v2_struct_0(B_126)
      | ~ l1_pre_topc(A_125)
      | v2_struct_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_369,c_16])).

tff(c_428,plain,(
    ! [A_128,A_129,B_130,B_131] :
      ( r1_tsep_1(A_128,k1_tsep_1(A_129,B_130,B_131))
      | ~ l1_struct_0(k1_tsep_1(A_129,B_130,B_131))
      | ~ r1_xboole_0(u1_struct_0(A_128),u1_struct_0(B_130))
      | ~ m1_pre_topc(B_131,A_129)
      | v2_struct_0(B_131)
      | ~ m1_pre_topc(B_130,A_129)
      | v2_struct_0(B_130)
      | ~ l1_pre_topc(A_129)
      | v2_struct_0(A_129)
      | ~ r1_tsep_1(A_128,B_131)
      | ~ l1_struct_0(B_131)
      | ~ l1_struct_0(A_128) ) ),
    inference(resolution,[status(thm)],[c_18,c_416])).

tff(c_440,plain,(
    ! [A_132,A_133,B_134,B_135] :
      ( r1_tsep_1(A_132,k1_tsep_1(A_133,B_134,B_135))
      | ~ l1_struct_0(k1_tsep_1(A_133,B_134,B_135))
      | ~ m1_pre_topc(B_135,A_133)
      | v2_struct_0(B_135)
      | ~ m1_pre_topc(B_134,A_133)
      | v2_struct_0(B_134)
      | ~ l1_pre_topc(A_133)
      | v2_struct_0(A_133)
      | ~ r1_tsep_1(A_132,B_135)
      | ~ l1_struct_0(B_135)
      | ~ r1_tsep_1(A_132,B_134)
      | ~ l1_struct_0(B_134)
      | ~ l1_struct_0(A_132) ) ),
    inference(resolution,[status(thm)],[c_18,c_428])).

tff(c_200,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_163,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_46,plain,
    ( ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ r1_tsep_1('#skF_2','#skF_4')
    | ~ r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ r1_tsep_1('#skF_4','#skF_3')
    | ~ r1_tsep_1('#skF_4','#skF_2')
    | ~ r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_224,plain,
    ( ~ r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_117,c_200,c_163,c_46])).

tff(c_225,plain,(
    ~ r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_452,plain,
    ( ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_3')
    | ~ r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_440,c_225])).

tff(c_461,plain,
    ( ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_201,c_186,c_164,c_117,c_40,c_36,c_32,c_452])).

tff(c_462,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_34,c_461])).

tff(c_467,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_462])).

tff(c_470,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_215,c_467])).

tff(c_473,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_32,c_470])).

tff(c_475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_34,c_473])).

tff(c_476,plain,(
    ~ r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_477,plain,(
    r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_479,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_477,c_26])).

tff(c_482,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_479])).

tff(c_483,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_476,c_482])).

tff(c_487,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_483])).

tff(c_490,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_215,c_487])).

tff(c_493,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_32,c_490])).

tff(c_495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_34,c_493])).

tff(c_497,plain,(
    ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_753,plain,(
    ! [A_198,B_199,C_200] :
      ( m1_pre_topc(k1_tsep_1(A_198,B_199,C_200),A_198)
      | ~ m1_pre_topc(C_200,A_198)
      | v2_struct_0(C_200)
      | ~ m1_pre_topc(B_199,A_198)
      | v2_struct_0(B_199)
      | ~ l1_pre_topc(A_198)
      | v2_struct_0(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_758,plain,(
    ! [A_201,B_202,C_203] :
      ( l1_pre_topc(k1_tsep_1(A_201,B_202,C_203))
      | ~ m1_pre_topc(C_203,A_201)
      | v2_struct_0(C_203)
      | ~ m1_pre_topc(B_202,A_201)
      | v2_struct_0(B_202)
      | ~ l1_pre_topc(A_201)
      | v2_struct_0(A_201) ) ),
    inference(resolution,[status(thm)],[c_753,c_10])).

tff(c_515,plain,(
    ! [A_142,B_143,C_144] :
      ( m1_pre_topc(k1_tsep_1(A_142,B_143,C_144),A_142)
      | ~ m1_pre_topc(C_144,A_142)
      | v2_struct_0(C_144)
      | ~ m1_pre_topc(B_143,A_142)
      | v2_struct_0(B_143)
      | ~ l1_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_522,plain,(
    ! [A_145,B_146,C_147] :
      ( l1_pre_topc(k1_tsep_1(A_145,B_146,C_147))
      | ~ m1_pre_topc(C_147,A_145)
      | v2_struct_0(C_147)
      | ~ m1_pre_topc(B_146,A_145)
      | v2_struct_0(B_146)
      | ~ l1_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(resolution,[status(thm)],[c_515,c_10])).

tff(c_496,plain,
    ( r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_498,plain,(
    r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_496])).

tff(c_500,plain,
    ( r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_498,c_26])).

tff(c_503,plain,
    ( r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_500])).

tff(c_504,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_503])).

tff(c_508,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_504])).

tff(c_525,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_522,c_508])).

tff(c_528,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_32,c_525])).

tff(c_530,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_34,c_528])).

tff(c_532,plain,(
    l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_503])).

tff(c_531,plain,(
    r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_503])).

tff(c_558,plain,(
    ! [A_164,B_165,C_166] :
      ( u1_struct_0(k1_tsep_1(A_164,B_165,C_166)) = k2_xboole_0(u1_struct_0(B_165),u1_struct_0(C_166))
      | ~ m1_pre_topc(k1_tsep_1(A_164,B_165,C_166),A_164)
      | ~ v1_pre_topc(k1_tsep_1(A_164,B_165,C_166))
      | v2_struct_0(k1_tsep_1(A_164,B_165,C_166))
      | ~ m1_pre_topc(C_166,A_164)
      | v2_struct_0(C_166)
      | ~ m1_pre_topc(B_165,A_164)
      | v2_struct_0(B_165)
      | ~ l1_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_562,plain,(
    ! [A_167,B_168,C_169] :
      ( u1_struct_0(k1_tsep_1(A_167,B_168,C_169)) = k2_xboole_0(u1_struct_0(B_168),u1_struct_0(C_169))
      | ~ v1_pre_topc(k1_tsep_1(A_167,B_168,C_169))
      | v2_struct_0(k1_tsep_1(A_167,B_168,C_169))
      | ~ m1_pre_topc(C_169,A_167)
      | v2_struct_0(C_169)
      | ~ m1_pre_topc(B_168,A_167)
      | v2_struct_0(B_168)
      | ~ l1_pre_topc(A_167)
      | v2_struct_0(A_167) ) ),
    inference(resolution,[status(thm)],[c_20,c_558])).

tff(c_622,plain,(
    ! [A_170,B_171,C_172] :
      ( u1_struct_0(k1_tsep_1(A_170,B_171,C_172)) = k2_xboole_0(u1_struct_0(B_171),u1_struct_0(C_172))
      | ~ v1_pre_topc(k1_tsep_1(A_170,B_171,C_172))
      | ~ m1_pre_topc(C_172,A_170)
      | v2_struct_0(C_172)
      | ~ m1_pre_topc(B_171,A_170)
      | v2_struct_0(B_171)
      | ~ l1_pre_topc(A_170)
      | v2_struct_0(A_170) ) ),
    inference(resolution,[status(thm)],[c_562,c_24])).

tff(c_626,plain,(
    ! [A_173,B_174,C_175] :
      ( u1_struct_0(k1_tsep_1(A_173,B_174,C_175)) = k2_xboole_0(u1_struct_0(B_174),u1_struct_0(C_175))
      | ~ m1_pre_topc(C_175,A_173)
      | v2_struct_0(C_175)
      | ~ m1_pre_topc(B_174,A_173)
      | v2_struct_0(B_174)
      | ~ l1_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(resolution,[status(thm)],[c_22,c_622])).

tff(c_6,plain,(
    ! [A_1,B_2,C_3] :
      ( r1_xboole_0(A_1,B_2)
      | ~ r1_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_691,plain,(
    ! [A_180,B_181,A_182,C_183] :
      ( r1_xboole_0(A_180,u1_struct_0(B_181))
      | ~ r1_xboole_0(A_180,u1_struct_0(k1_tsep_1(A_182,B_181,C_183)))
      | ~ m1_pre_topc(C_183,A_182)
      | v2_struct_0(C_183)
      | ~ m1_pre_topc(B_181,A_182)
      | v2_struct_0(B_181)
      | ~ l1_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_626,c_6])).

tff(c_717,plain,(
    ! [A_188,B_189,C_190,A_191] :
      ( r1_xboole_0(u1_struct_0(A_188),u1_struct_0(B_189))
      | ~ m1_pre_topc(C_190,A_191)
      | v2_struct_0(C_190)
      | ~ m1_pre_topc(B_189,A_191)
      | v2_struct_0(B_189)
      | ~ l1_pre_topc(A_191)
      | v2_struct_0(A_191)
      | ~ r1_tsep_1(A_188,k1_tsep_1(A_191,B_189,C_190))
      | ~ l1_struct_0(k1_tsep_1(A_191,B_189,C_190))
      | ~ l1_struct_0(A_188) ) ),
    inference(resolution,[status(thm)],[c_18,c_691])).

tff(c_719,plain,
    ( r1_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_531,c_717])).

tff(c_722,plain,
    ( r1_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_532,c_40,c_36,c_32,c_719])).

tff(c_723,plain,(
    r1_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_34,c_722])).

tff(c_726,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_723,c_16])).

tff(c_729,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_726])).

tff(c_730,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_497,c_729])).

tff(c_733,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_730])).

tff(c_737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_733])).

tff(c_739,plain,(
    ~ r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_496])).

tff(c_738,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_496])).

tff(c_740,plain,(
    r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_738])).

tff(c_742,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_740,c_26])).

tff(c_745,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_742])).

tff(c_746,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_739,c_745])).

tff(c_750,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_746])).

tff(c_761,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_758,c_750])).

tff(c_764,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_32,c_761])).

tff(c_766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_34,c_764])).

tff(c_767,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_738])).

tff(c_773,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_767,c_26])).

tff(c_776,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_773])).

tff(c_777,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_497,c_776])).

tff(c_780,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_777])).

tff(c_784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_780])).

tff(c_786,plain,(
    ~ r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_1144,plain,(
    ! [A_300,B_301,C_302] :
      ( m1_pre_topc(k1_tsep_1(A_300,B_301,C_302),A_300)
      | ~ m1_pre_topc(C_302,A_300)
      | v2_struct_0(C_302)
      | ~ m1_pre_topc(B_301,A_300)
      | v2_struct_0(B_301)
      | ~ l1_pre_topc(A_300)
      | v2_struct_0(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1149,plain,(
    ! [A_303,B_304,C_305] :
      ( l1_pre_topc(k1_tsep_1(A_303,B_304,C_305))
      | ~ m1_pre_topc(C_305,A_303)
      | v2_struct_0(C_305)
      | ~ m1_pre_topc(B_304,A_303)
      | v2_struct_0(B_304)
      | ~ l1_pre_topc(A_303)
      | v2_struct_0(A_303) ) ),
    inference(resolution,[status(thm)],[c_1144,c_10])).

tff(c_88,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_808,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_786,c_88])).

tff(c_809,plain,(
    r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_808])).

tff(c_811,plain,(
    ! [B_213,A_214] :
      ( r1_tsep_1(B_213,A_214)
      | ~ r1_tsep_1(A_214,B_213)
      | ~ l1_struct_0(B_213)
      | ~ l1_struct_0(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_814,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_809,c_811])).

tff(c_830,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_814])).

tff(c_833,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_830])).

tff(c_837,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_803,c_833])).

tff(c_839,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_814])).

tff(c_850,plain,(
    ! [A_228,B_229,C_230] :
      ( m1_pre_topc(k1_tsep_1(A_228,B_229,C_230),A_228)
      | ~ m1_pre_topc(C_230,A_228)
      | v2_struct_0(C_230)
      | ~ m1_pre_topc(B_229,A_228)
      | v2_struct_0(B_229)
      | ~ l1_pre_topc(A_228)
      | v2_struct_0(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_855,plain,(
    ! [A_231,B_232,C_233] :
      ( l1_pre_topc(k1_tsep_1(A_231,B_232,C_233))
      | ~ m1_pre_topc(C_233,A_231)
      | v2_struct_0(C_233)
      | ~ m1_pre_topc(B_232,A_231)
      | v2_struct_0(B_232)
      | ~ l1_pre_topc(A_231)
      | v2_struct_0(A_231) ) ),
    inference(resolution,[status(thm)],[c_850,c_10])).

tff(c_838,plain,
    ( ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_814])).

tff(c_841,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_838])).

tff(c_845,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_841])).

tff(c_858,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_855,c_845])).

tff(c_861,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_32,c_858])).

tff(c_863,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_34,c_861])).

tff(c_865,plain,(
    l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_838])).

tff(c_893,plain,(
    ! [A_250,B_251,C_252] :
      ( u1_struct_0(k1_tsep_1(A_250,B_251,C_252)) = k2_xboole_0(u1_struct_0(B_251),u1_struct_0(C_252))
      | ~ m1_pre_topc(k1_tsep_1(A_250,B_251,C_252),A_250)
      | ~ v1_pre_topc(k1_tsep_1(A_250,B_251,C_252))
      | v2_struct_0(k1_tsep_1(A_250,B_251,C_252))
      | ~ m1_pre_topc(C_252,A_250)
      | v2_struct_0(C_252)
      | ~ m1_pre_topc(B_251,A_250)
      | v2_struct_0(B_251)
      | ~ l1_pre_topc(A_250)
      | v2_struct_0(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_897,plain,(
    ! [A_253,B_254,C_255] :
      ( u1_struct_0(k1_tsep_1(A_253,B_254,C_255)) = k2_xboole_0(u1_struct_0(B_254),u1_struct_0(C_255))
      | ~ v1_pre_topc(k1_tsep_1(A_253,B_254,C_255))
      | v2_struct_0(k1_tsep_1(A_253,B_254,C_255))
      | ~ m1_pre_topc(C_255,A_253)
      | v2_struct_0(C_255)
      | ~ m1_pre_topc(B_254,A_253)
      | v2_struct_0(B_254)
      | ~ l1_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(resolution,[status(thm)],[c_20,c_893])).

tff(c_957,plain,(
    ! [A_256,B_257,C_258] :
      ( u1_struct_0(k1_tsep_1(A_256,B_257,C_258)) = k2_xboole_0(u1_struct_0(B_257),u1_struct_0(C_258))
      | ~ v1_pre_topc(k1_tsep_1(A_256,B_257,C_258))
      | ~ m1_pre_topc(C_258,A_256)
      | v2_struct_0(C_258)
      | ~ m1_pre_topc(B_257,A_256)
      | v2_struct_0(B_257)
      | ~ l1_pre_topc(A_256)
      | v2_struct_0(A_256) ) ),
    inference(resolution,[status(thm)],[c_897,c_24])).

tff(c_961,plain,(
    ! [A_259,B_260,C_261] :
      ( u1_struct_0(k1_tsep_1(A_259,B_260,C_261)) = k2_xboole_0(u1_struct_0(B_260),u1_struct_0(C_261))
      | ~ m1_pre_topc(C_261,A_259)
      | v2_struct_0(C_261)
      | ~ m1_pre_topc(B_260,A_259)
      | v2_struct_0(B_260)
      | ~ l1_pre_topc(A_259)
      | v2_struct_0(A_259) ) ),
    inference(resolution,[status(thm)],[c_22,c_957])).

tff(c_4,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1017,plain,(
    ! [A_262,C_263,A_264,B_265] :
      ( r1_xboole_0(A_262,u1_struct_0(C_263))
      | ~ r1_xboole_0(A_262,u1_struct_0(k1_tsep_1(A_264,B_265,C_263)))
      | ~ m1_pre_topc(C_263,A_264)
      | v2_struct_0(C_263)
      | ~ m1_pre_topc(B_265,A_264)
      | v2_struct_0(B_265)
      | ~ l1_pre_topc(A_264)
      | v2_struct_0(A_264) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_961,c_4])).

tff(c_1085,plain,(
    ! [A_278,C_279,A_280,B_281] :
      ( r1_xboole_0(u1_struct_0(A_278),u1_struct_0(C_279))
      | ~ m1_pre_topc(C_279,A_280)
      | v2_struct_0(C_279)
      | ~ m1_pre_topc(B_281,A_280)
      | v2_struct_0(B_281)
      | ~ l1_pre_topc(A_280)
      | v2_struct_0(A_280)
      | ~ r1_tsep_1(A_278,k1_tsep_1(A_280,B_281,C_279))
      | ~ l1_struct_0(k1_tsep_1(A_280,B_281,C_279))
      | ~ l1_struct_0(A_278) ) ),
    inference(resolution,[status(thm)],[c_18,c_1017])).

tff(c_1087,plain,
    ( r1_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_809,c_1085])).

tff(c_1090,plain,
    ( r1_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_865,c_40,c_36,c_32,c_1087])).

tff(c_1091,plain,(
    r1_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_34,c_1090])).

tff(c_1094,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1091,c_16])).

tff(c_1097,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_1094])).

tff(c_1098,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_786,c_1097])).

tff(c_1101,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_1098])).

tff(c_1105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_1101])).

tff(c_1107,plain,(
    ~ r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_808])).

tff(c_1106,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_808])).

tff(c_1109,plain,(
    r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1106])).

tff(c_1110,plain,(
    ! [B_285,A_286] :
      ( r1_tsep_1(B_285,A_286)
      | ~ r1_tsep_1(A_286,B_285)
      | ~ l1_struct_0(B_285)
      | ~ l1_struct_0(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1112,plain,
    ( r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1109,c_1110])).

tff(c_1115,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1107,c_1112])).

tff(c_1116,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1115])).

tff(c_1120,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_1116])).

tff(c_1152,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1149,c_1120])).

tff(c_1155,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_32,c_1152])).

tff(c_1157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_34,c_1155])).

tff(c_1158,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1115])).

tff(c_1164,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_1158])).

tff(c_1168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_803,c_1164])).

tff(c_1169,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1106])).

tff(c_1171,plain,(
    ! [B_306,A_307] :
      ( r1_tsep_1(B_306,A_307)
      | ~ r1_tsep_1(A_307,B_306)
      | ~ l1_struct_0(B_306)
      | ~ l1_struct_0(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1173,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1169,c_1171])).

tff(c_1176,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_786,c_1173])).

tff(c_1177,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1176])).

tff(c_1189,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_1177])).

tff(c_1193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_1189])).

tff(c_1194,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1176])).

tff(c_1198,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_1194])).

tff(c_1202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_803,c_1198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.32/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.78  
% 4.37/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.78  %$ r1_xboole_0 > r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.37/1.78  
% 4.37/1.78  %Foreground sorts:
% 4.37/1.78  
% 4.37/1.78  
% 4.37/1.78  %Background operators:
% 4.37/1.78  
% 4.37/1.78  
% 4.37/1.78  %Foreground operators:
% 4.37/1.78  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.37/1.78  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 4.37/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.37/1.78  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.37/1.78  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.37/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.37/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.37/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.37/1.78  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.37/1.78  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.37/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.37/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.37/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.37/1.78  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.37/1.78  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.37/1.78  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 4.37/1.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.37/1.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.37/1.78  
% 4.61/1.81  tff(f_170, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((((r1_tsep_1(k1_tsep_1(A, B, C), D) => (r1_tsep_1(B, D) & r1_tsep_1(C, D))) & ((r1_tsep_1(B, D) & r1_tsep_1(C, D)) => r1_tsep_1(k1_tsep_1(A, B, C), D))) & (r1_tsep_1(D, k1_tsep_1(A, B, C)) => (r1_tsep_1(D, B) & r1_tsep_1(D, C)))) & ((r1_tsep_1(D, B) & r1_tsep_1(D, C)) => r1_tsep_1(D, k1_tsep_1(A, B, C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_tmap_1)).
% 4.61/1.81  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.61/1.81  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.61/1.81  tff(f_112, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 4.61/1.81  tff(f_120, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 4.61/1.81  tff(f_90, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 4.61/1.81  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k1_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k2_xboole_0(u1_struct_0(B), u1_struct_0(C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tsep_1)).
% 4.61/1.81  tff(f_41, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 4.61/1.81  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.61/1.81  tff(c_28, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.61/1.81  tff(c_788, plain, (![B_205, A_206]: (l1_pre_topc(B_205) | ~m1_pre_topc(B_205, A_206) | ~l1_pre_topc(A_206))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.61/1.81  tff(c_794, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_788])).
% 4.61/1.81  tff(c_803, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_794])).
% 4.61/1.81  tff(c_8, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.61/1.81  tff(c_32, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.61/1.81  tff(c_791, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_788])).
% 4.61/1.81  tff(c_800, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_791])).
% 4.61/1.81  tff(c_36, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.61/1.81  tff(c_119, plain, (![B_43, A_44]: (l1_pre_topc(B_43) | ~m1_pre_topc(B_43, A_44) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.61/1.81  tff(c_128, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_119])).
% 4.61/1.81  tff(c_137, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_128])).
% 4.61/1.81  tff(c_44, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.61/1.81  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.61/1.81  tff(c_34, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.61/1.81  tff(c_211, plain, (![A_66, B_67, C_68]: (m1_pre_topc(k1_tsep_1(A_66, B_67, C_68), A_66) | ~m1_pre_topc(C_68, A_66) | v2_struct_0(C_68) | ~m1_pre_topc(B_67, A_66) | v2_struct_0(B_67) | ~l1_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.61/1.81  tff(c_10, plain, (![B_7, A_5]: (l1_pre_topc(B_7) | ~m1_pre_topc(B_7, A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.61/1.81  tff(c_215, plain, (![A_66, B_67, C_68]: (l1_pre_topc(k1_tsep_1(A_66, B_67, C_68)) | ~m1_pre_topc(C_68, A_66) | v2_struct_0(C_68) | ~m1_pre_topc(B_67, A_66) | v2_struct_0(B_67) | ~l1_pre_topc(A_66) | v2_struct_0(A_66))), inference(resolution, [status(thm)], [c_211, c_10])).
% 4.61/1.81  tff(c_125, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_119])).
% 4.61/1.81  tff(c_134, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_125])).
% 4.61/1.81  tff(c_92, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.61/1.81  tff(c_117, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_92])).
% 4.61/1.81  tff(c_140, plain, (![B_51, A_52]: (r1_tsep_1(B_51, A_52) | ~r1_tsep_1(A_52, B_51) | ~l1_struct_0(B_51) | ~l1_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.61/1.81  tff(c_143, plain, (r1_tsep_1('#skF_3', '#skF_4') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_117, c_140])).
% 4.61/1.81  tff(c_145, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_143])).
% 4.61/1.81  tff(c_148, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8, c_145])).
% 4.61/1.81  tff(c_152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_148])).
% 4.61/1.81  tff(c_154, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_143])).
% 4.61/1.81  tff(c_116, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.61/1.81  tff(c_186, plain, (r1_tsep_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_116])).
% 4.61/1.81  tff(c_26, plain, (![B_30, A_29]: (r1_tsep_1(B_30, A_29) | ~r1_tsep_1(A_29, B_30) | ~l1_struct_0(B_30) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.61/1.81  tff(c_188, plain, (r1_tsep_1('#skF_2', '#skF_4') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_186, c_26])).
% 4.61/1.81  tff(c_191, plain, (r1_tsep_1('#skF_2', '#skF_4') | ~l1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_188])).
% 4.61/1.81  tff(c_192, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_191])).
% 4.61/1.81  tff(c_195, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_192])).
% 4.61/1.81  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_195])).
% 4.61/1.81  tff(c_201, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_191])).
% 4.61/1.81  tff(c_122, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_119])).
% 4.61/1.81  tff(c_131, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_122])).
% 4.61/1.81  tff(c_153, plain, (~l1_struct_0('#skF_3') | r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_143])).
% 4.61/1.81  tff(c_155, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_153])).
% 4.61/1.81  tff(c_158, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8, c_155])).
% 4.61/1.81  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_158])).
% 4.61/1.81  tff(c_164, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_153])).
% 4.61/1.81  tff(c_18, plain, (![A_23, B_25]: (r1_xboole_0(u1_struct_0(A_23), u1_struct_0(B_25)) | ~r1_tsep_1(A_23, B_25) | ~l1_struct_0(B_25) | ~l1_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.61/1.81  tff(c_22, plain, (![A_26, B_27, C_28]: (v1_pre_topc(k1_tsep_1(A_26, B_27, C_28)) | ~m1_pre_topc(C_28, A_26) | v2_struct_0(C_28) | ~m1_pre_topc(B_27, A_26) | v2_struct_0(B_27) | ~l1_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.61/1.81  tff(c_20, plain, (![A_26, B_27, C_28]: (m1_pre_topc(k1_tsep_1(A_26, B_27, C_28), A_26) | ~m1_pre_topc(C_28, A_26) | v2_struct_0(C_28) | ~m1_pre_topc(B_27, A_26) | v2_struct_0(B_27) | ~l1_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.61/1.81  tff(c_227, plain, (![A_76, B_77, C_78]: (u1_struct_0(k1_tsep_1(A_76, B_77, C_78))=k2_xboole_0(u1_struct_0(B_77), u1_struct_0(C_78)) | ~m1_pre_topc(k1_tsep_1(A_76, B_77, C_78), A_76) | ~v1_pre_topc(k1_tsep_1(A_76, B_77, C_78)) | v2_struct_0(k1_tsep_1(A_76, B_77, C_78)) | ~m1_pre_topc(C_78, A_76) | v2_struct_0(C_78) | ~m1_pre_topc(B_77, A_76) | v2_struct_0(B_77) | ~l1_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.61/1.81  tff(c_231, plain, (![A_79, B_80, C_81]: (u1_struct_0(k1_tsep_1(A_79, B_80, C_81))=k2_xboole_0(u1_struct_0(B_80), u1_struct_0(C_81)) | ~v1_pre_topc(k1_tsep_1(A_79, B_80, C_81)) | v2_struct_0(k1_tsep_1(A_79, B_80, C_81)) | ~m1_pre_topc(C_81, A_79) | v2_struct_0(C_81) | ~m1_pre_topc(B_80, A_79) | v2_struct_0(B_80) | ~l1_pre_topc(A_79) | v2_struct_0(A_79))), inference(resolution, [status(thm)], [c_20, c_227])).
% 4.61/1.81  tff(c_24, plain, (![A_26, B_27, C_28]: (~v2_struct_0(k1_tsep_1(A_26, B_27, C_28)) | ~m1_pre_topc(C_28, A_26) | v2_struct_0(C_28) | ~m1_pre_topc(B_27, A_26) | v2_struct_0(B_27) | ~l1_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.61/1.81  tff(c_291, plain, (![A_82, B_83, C_84]: (u1_struct_0(k1_tsep_1(A_82, B_83, C_84))=k2_xboole_0(u1_struct_0(B_83), u1_struct_0(C_84)) | ~v1_pre_topc(k1_tsep_1(A_82, B_83, C_84)) | ~m1_pre_topc(C_84, A_82) | v2_struct_0(C_84) | ~m1_pre_topc(B_83, A_82) | v2_struct_0(B_83) | ~l1_pre_topc(A_82) | v2_struct_0(A_82))), inference(resolution, [status(thm)], [c_231, c_24])).
% 4.61/1.81  tff(c_295, plain, (![A_85, B_86, C_87]: (u1_struct_0(k1_tsep_1(A_85, B_86, C_87))=k2_xboole_0(u1_struct_0(B_86), u1_struct_0(C_87)) | ~m1_pre_topc(C_87, A_85) | v2_struct_0(C_87) | ~m1_pre_topc(B_86, A_85) | v2_struct_0(B_86) | ~l1_pre_topc(A_85) | v2_struct_0(A_85))), inference(resolution, [status(thm)], [c_22, c_291])).
% 4.61/1.81  tff(c_2, plain, (![A_1, C_3, B_2]: (~r1_xboole_0(A_1, C_3) | ~r1_xboole_0(A_1, B_2) | r1_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.61/1.81  tff(c_369, plain, (![A_96, C_97, B_98, A_99]: (~r1_xboole_0(A_96, u1_struct_0(C_97)) | ~r1_xboole_0(A_96, u1_struct_0(B_98)) | r1_xboole_0(A_96, u1_struct_0(k1_tsep_1(A_99, B_98, C_97))) | ~m1_pre_topc(C_97, A_99) | v2_struct_0(C_97) | ~m1_pre_topc(B_98, A_99) | v2_struct_0(B_98) | ~l1_pre_topc(A_99) | v2_struct_0(A_99))), inference(superposition, [status(thm), theory('equality')], [c_295, c_2])).
% 4.61/1.81  tff(c_16, plain, (![A_23, B_25]: (r1_tsep_1(A_23, B_25) | ~r1_xboole_0(u1_struct_0(A_23), u1_struct_0(B_25)) | ~l1_struct_0(B_25) | ~l1_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.61/1.81  tff(c_416, plain, (![A_124, A_125, B_126, C_127]: (r1_tsep_1(A_124, k1_tsep_1(A_125, B_126, C_127)) | ~l1_struct_0(k1_tsep_1(A_125, B_126, C_127)) | ~l1_struct_0(A_124) | ~r1_xboole_0(u1_struct_0(A_124), u1_struct_0(C_127)) | ~r1_xboole_0(u1_struct_0(A_124), u1_struct_0(B_126)) | ~m1_pre_topc(C_127, A_125) | v2_struct_0(C_127) | ~m1_pre_topc(B_126, A_125) | v2_struct_0(B_126) | ~l1_pre_topc(A_125) | v2_struct_0(A_125))), inference(resolution, [status(thm)], [c_369, c_16])).
% 4.61/1.81  tff(c_428, plain, (![A_128, A_129, B_130, B_131]: (r1_tsep_1(A_128, k1_tsep_1(A_129, B_130, B_131)) | ~l1_struct_0(k1_tsep_1(A_129, B_130, B_131)) | ~r1_xboole_0(u1_struct_0(A_128), u1_struct_0(B_130)) | ~m1_pre_topc(B_131, A_129) | v2_struct_0(B_131) | ~m1_pre_topc(B_130, A_129) | v2_struct_0(B_130) | ~l1_pre_topc(A_129) | v2_struct_0(A_129) | ~r1_tsep_1(A_128, B_131) | ~l1_struct_0(B_131) | ~l1_struct_0(A_128))), inference(resolution, [status(thm)], [c_18, c_416])).
% 4.61/1.81  tff(c_440, plain, (![A_132, A_133, B_134, B_135]: (r1_tsep_1(A_132, k1_tsep_1(A_133, B_134, B_135)) | ~l1_struct_0(k1_tsep_1(A_133, B_134, B_135)) | ~m1_pre_topc(B_135, A_133) | v2_struct_0(B_135) | ~m1_pre_topc(B_134, A_133) | v2_struct_0(B_134) | ~l1_pre_topc(A_133) | v2_struct_0(A_133) | ~r1_tsep_1(A_132, B_135) | ~l1_struct_0(B_135) | ~r1_tsep_1(A_132, B_134) | ~l1_struct_0(B_134) | ~l1_struct_0(A_132))), inference(resolution, [status(thm)], [c_18, c_428])).
% 4.61/1.81  tff(c_200, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_191])).
% 4.61/1.81  tff(c_163, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_153])).
% 4.61/1.81  tff(c_46, plain, (~r1_tsep_1('#skF_3', '#skF_4') | ~r1_tsep_1('#skF_2', '#skF_4') | ~r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | ~r1_tsep_1('#skF_4', '#skF_3') | ~r1_tsep_1('#skF_4', '#skF_2') | ~r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.61/1.81  tff(c_224, plain, (~r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | ~r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_117, c_200, c_163, c_46])).
% 4.61/1.81  tff(c_225, plain, (~r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_224])).
% 4.61/1.81  tff(c_452, plain, (~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_3') | ~r1_tsep_1('#skF_4', '#skF_2') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_440, c_225])).
% 4.61/1.81  tff(c_461, plain, (~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_201, c_186, c_164, c_117, c_40, c_36, c_32, c_452])).
% 4.61/1.81  tff(c_462, plain, (~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_34, c_461])).
% 4.61/1.81  tff(c_467, plain, (~l1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_462])).
% 4.61/1.81  tff(c_470, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_215, c_467])).
% 4.61/1.81  tff(c_473, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_32, c_470])).
% 4.61/1.81  tff(c_475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_34, c_473])).
% 4.61/1.81  tff(c_476, plain, (~r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_224])).
% 4.61/1.81  tff(c_477, plain, (r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_224])).
% 4.61/1.81  tff(c_479, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | ~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_477, c_26])).
% 4.61/1.81  tff(c_482, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | ~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_479])).
% 4.61/1.81  tff(c_483, plain, (~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_476, c_482])).
% 4.61/1.81  tff(c_487, plain, (~l1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_483])).
% 4.61/1.81  tff(c_490, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_215, c_487])).
% 4.61/1.81  tff(c_493, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_32, c_490])).
% 4.61/1.81  tff(c_495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_34, c_493])).
% 4.61/1.81  tff(c_497, plain, (~r1_tsep_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_116])).
% 4.61/1.81  tff(c_753, plain, (![A_198, B_199, C_200]: (m1_pre_topc(k1_tsep_1(A_198, B_199, C_200), A_198) | ~m1_pre_topc(C_200, A_198) | v2_struct_0(C_200) | ~m1_pre_topc(B_199, A_198) | v2_struct_0(B_199) | ~l1_pre_topc(A_198) | v2_struct_0(A_198))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.61/1.81  tff(c_758, plain, (![A_201, B_202, C_203]: (l1_pre_topc(k1_tsep_1(A_201, B_202, C_203)) | ~m1_pre_topc(C_203, A_201) | v2_struct_0(C_203) | ~m1_pre_topc(B_202, A_201) | v2_struct_0(B_202) | ~l1_pre_topc(A_201) | v2_struct_0(A_201))), inference(resolution, [status(thm)], [c_753, c_10])).
% 4.61/1.81  tff(c_515, plain, (![A_142, B_143, C_144]: (m1_pre_topc(k1_tsep_1(A_142, B_143, C_144), A_142) | ~m1_pre_topc(C_144, A_142) | v2_struct_0(C_144) | ~m1_pre_topc(B_143, A_142) | v2_struct_0(B_143) | ~l1_pre_topc(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.61/1.81  tff(c_522, plain, (![A_145, B_146, C_147]: (l1_pre_topc(k1_tsep_1(A_145, B_146, C_147)) | ~m1_pre_topc(C_147, A_145) | v2_struct_0(C_147) | ~m1_pre_topc(B_146, A_145) | v2_struct_0(B_146) | ~l1_pre_topc(A_145) | v2_struct_0(A_145))), inference(resolution, [status(thm)], [c_515, c_10])).
% 4.61/1.81  tff(c_496, plain, (r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_116])).
% 4.61/1.81  tff(c_498, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_496])).
% 4.61/1.81  tff(c_500, plain, (r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~l1_struct_0('#skF_4') | ~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_498, c_26])).
% 4.61/1.81  tff(c_503, plain, (r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_500])).
% 4.61/1.81  tff(c_504, plain, (~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_503])).
% 4.61/1.81  tff(c_508, plain, (~l1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_504])).
% 4.61/1.81  tff(c_525, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_522, c_508])).
% 4.61/1.81  tff(c_528, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_32, c_525])).
% 4.61/1.81  tff(c_530, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_34, c_528])).
% 4.61/1.81  tff(c_532, plain, (l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_503])).
% 4.61/1.81  tff(c_531, plain, (r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_503])).
% 4.61/1.81  tff(c_558, plain, (![A_164, B_165, C_166]: (u1_struct_0(k1_tsep_1(A_164, B_165, C_166))=k2_xboole_0(u1_struct_0(B_165), u1_struct_0(C_166)) | ~m1_pre_topc(k1_tsep_1(A_164, B_165, C_166), A_164) | ~v1_pre_topc(k1_tsep_1(A_164, B_165, C_166)) | v2_struct_0(k1_tsep_1(A_164, B_165, C_166)) | ~m1_pre_topc(C_166, A_164) | v2_struct_0(C_166) | ~m1_pre_topc(B_165, A_164) | v2_struct_0(B_165) | ~l1_pre_topc(A_164) | v2_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.61/1.81  tff(c_562, plain, (![A_167, B_168, C_169]: (u1_struct_0(k1_tsep_1(A_167, B_168, C_169))=k2_xboole_0(u1_struct_0(B_168), u1_struct_0(C_169)) | ~v1_pre_topc(k1_tsep_1(A_167, B_168, C_169)) | v2_struct_0(k1_tsep_1(A_167, B_168, C_169)) | ~m1_pre_topc(C_169, A_167) | v2_struct_0(C_169) | ~m1_pre_topc(B_168, A_167) | v2_struct_0(B_168) | ~l1_pre_topc(A_167) | v2_struct_0(A_167))), inference(resolution, [status(thm)], [c_20, c_558])).
% 4.61/1.81  tff(c_622, plain, (![A_170, B_171, C_172]: (u1_struct_0(k1_tsep_1(A_170, B_171, C_172))=k2_xboole_0(u1_struct_0(B_171), u1_struct_0(C_172)) | ~v1_pre_topc(k1_tsep_1(A_170, B_171, C_172)) | ~m1_pre_topc(C_172, A_170) | v2_struct_0(C_172) | ~m1_pre_topc(B_171, A_170) | v2_struct_0(B_171) | ~l1_pre_topc(A_170) | v2_struct_0(A_170))), inference(resolution, [status(thm)], [c_562, c_24])).
% 4.61/1.81  tff(c_626, plain, (![A_173, B_174, C_175]: (u1_struct_0(k1_tsep_1(A_173, B_174, C_175))=k2_xboole_0(u1_struct_0(B_174), u1_struct_0(C_175)) | ~m1_pre_topc(C_175, A_173) | v2_struct_0(C_175) | ~m1_pre_topc(B_174, A_173) | v2_struct_0(B_174) | ~l1_pre_topc(A_173) | v2_struct_0(A_173))), inference(resolution, [status(thm)], [c_22, c_622])).
% 4.61/1.81  tff(c_6, plain, (![A_1, B_2, C_3]: (r1_xboole_0(A_1, B_2) | ~r1_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.61/1.81  tff(c_691, plain, (![A_180, B_181, A_182, C_183]: (r1_xboole_0(A_180, u1_struct_0(B_181)) | ~r1_xboole_0(A_180, u1_struct_0(k1_tsep_1(A_182, B_181, C_183))) | ~m1_pre_topc(C_183, A_182) | v2_struct_0(C_183) | ~m1_pre_topc(B_181, A_182) | v2_struct_0(B_181) | ~l1_pre_topc(A_182) | v2_struct_0(A_182))), inference(superposition, [status(thm), theory('equality')], [c_626, c_6])).
% 4.61/1.81  tff(c_717, plain, (![A_188, B_189, C_190, A_191]: (r1_xboole_0(u1_struct_0(A_188), u1_struct_0(B_189)) | ~m1_pre_topc(C_190, A_191) | v2_struct_0(C_190) | ~m1_pre_topc(B_189, A_191) | v2_struct_0(B_189) | ~l1_pre_topc(A_191) | v2_struct_0(A_191) | ~r1_tsep_1(A_188, k1_tsep_1(A_191, B_189, C_190)) | ~l1_struct_0(k1_tsep_1(A_191, B_189, C_190)) | ~l1_struct_0(A_188))), inference(resolution, [status(thm)], [c_18, c_691])).
% 4.61/1.81  tff(c_719, plain, (r1_xboole_0(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_531, c_717])).
% 4.61/1.81  tff(c_722, plain, (r1_xboole_0(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_532, c_40, c_36, c_32, c_719])).
% 4.61/1.81  tff(c_723, plain, (r1_xboole_0(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_34, c_722])).
% 4.61/1.81  tff(c_726, plain, (r1_tsep_1('#skF_4', '#skF_2') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_723, c_16])).
% 4.61/1.81  tff(c_729, plain, (r1_tsep_1('#skF_4', '#skF_2') | ~l1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_726])).
% 4.61/1.81  tff(c_730, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_497, c_729])).
% 4.61/1.81  tff(c_733, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_730])).
% 4.61/1.81  tff(c_737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_733])).
% 4.61/1.81  tff(c_739, plain, (~r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_496])).
% 4.61/1.81  tff(c_738, plain, (r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_496])).
% 4.61/1.81  tff(c_740, plain, (r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_738])).
% 4.61/1.81  tff(c_742, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | ~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_740, c_26])).
% 4.61/1.81  tff(c_745, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | ~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_742])).
% 4.61/1.81  tff(c_746, plain, (~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_739, c_745])).
% 4.61/1.81  tff(c_750, plain, (~l1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_746])).
% 4.61/1.81  tff(c_761, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_758, c_750])).
% 4.61/1.81  tff(c_764, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_32, c_761])).
% 4.61/1.81  tff(c_766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_34, c_764])).
% 4.61/1.81  tff(c_767, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_738])).
% 4.61/1.81  tff(c_773, plain, (r1_tsep_1('#skF_4', '#skF_2') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_767, c_26])).
% 4.61/1.81  tff(c_776, plain, (r1_tsep_1('#skF_4', '#skF_2') | ~l1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_773])).
% 4.61/1.81  tff(c_777, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_497, c_776])).
% 4.61/1.81  tff(c_780, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_777])).
% 4.61/1.81  tff(c_784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_780])).
% 4.61/1.81  tff(c_786, plain, (~r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_92])).
% 4.61/1.81  tff(c_1144, plain, (![A_300, B_301, C_302]: (m1_pre_topc(k1_tsep_1(A_300, B_301, C_302), A_300) | ~m1_pre_topc(C_302, A_300) | v2_struct_0(C_302) | ~m1_pre_topc(B_301, A_300) | v2_struct_0(B_301) | ~l1_pre_topc(A_300) | v2_struct_0(A_300))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.61/1.81  tff(c_1149, plain, (![A_303, B_304, C_305]: (l1_pre_topc(k1_tsep_1(A_303, B_304, C_305)) | ~m1_pre_topc(C_305, A_303) | v2_struct_0(C_305) | ~m1_pre_topc(B_304, A_303) | v2_struct_0(B_304) | ~l1_pre_topc(A_303) | v2_struct_0(A_303))), inference(resolution, [status(thm)], [c_1144, c_10])).
% 4.61/1.81  tff(c_88, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.61/1.81  tff(c_808, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_786, c_88])).
% 4.61/1.81  tff(c_809, plain, (r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_808])).
% 4.61/1.81  tff(c_811, plain, (![B_213, A_214]: (r1_tsep_1(B_213, A_214) | ~r1_tsep_1(A_214, B_213) | ~l1_struct_0(B_213) | ~l1_struct_0(A_214))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.61/1.81  tff(c_814, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | ~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_809, c_811])).
% 4.61/1.81  tff(c_830, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_814])).
% 4.61/1.81  tff(c_833, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8, c_830])).
% 4.61/1.81  tff(c_837, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_803, c_833])).
% 4.61/1.81  tff(c_839, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_814])).
% 4.61/1.81  tff(c_850, plain, (![A_228, B_229, C_230]: (m1_pre_topc(k1_tsep_1(A_228, B_229, C_230), A_228) | ~m1_pre_topc(C_230, A_228) | v2_struct_0(C_230) | ~m1_pre_topc(B_229, A_228) | v2_struct_0(B_229) | ~l1_pre_topc(A_228) | v2_struct_0(A_228))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.61/1.81  tff(c_855, plain, (![A_231, B_232, C_233]: (l1_pre_topc(k1_tsep_1(A_231, B_232, C_233)) | ~m1_pre_topc(C_233, A_231) | v2_struct_0(C_233) | ~m1_pre_topc(B_232, A_231) | v2_struct_0(B_232) | ~l1_pre_topc(A_231) | v2_struct_0(A_231))), inference(resolution, [status(thm)], [c_850, c_10])).
% 4.61/1.81  tff(c_838, plain, (~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_814])).
% 4.61/1.81  tff(c_841, plain, (~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_838])).
% 4.61/1.81  tff(c_845, plain, (~l1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_841])).
% 4.61/1.81  tff(c_858, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_855, c_845])).
% 4.61/1.81  tff(c_861, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_32, c_858])).
% 4.61/1.81  tff(c_863, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_34, c_861])).
% 4.61/1.81  tff(c_865, plain, (l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_838])).
% 4.61/1.81  tff(c_893, plain, (![A_250, B_251, C_252]: (u1_struct_0(k1_tsep_1(A_250, B_251, C_252))=k2_xboole_0(u1_struct_0(B_251), u1_struct_0(C_252)) | ~m1_pre_topc(k1_tsep_1(A_250, B_251, C_252), A_250) | ~v1_pre_topc(k1_tsep_1(A_250, B_251, C_252)) | v2_struct_0(k1_tsep_1(A_250, B_251, C_252)) | ~m1_pre_topc(C_252, A_250) | v2_struct_0(C_252) | ~m1_pre_topc(B_251, A_250) | v2_struct_0(B_251) | ~l1_pre_topc(A_250) | v2_struct_0(A_250))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.61/1.81  tff(c_897, plain, (![A_253, B_254, C_255]: (u1_struct_0(k1_tsep_1(A_253, B_254, C_255))=k2_xboole_0(u1_struct_0(B_254), u1_struct_0(C_255)) | ~v1_pre_topc(k1_tsep_1(A_253, B_254, C_255)) | v2_struct_0(k1_tsep_1(A_253, B_254, C_255)) | ~m1_pre_topc(C_255, A_253) | v2_struct_0(C_255) | ~m1_pre_topc(B_254, A_253) | v2_struct_0(B_254) | ~l1_pre_topc(A_253) | v2_struct_0(A_253))), inference(resolution, [status(thm)], [c_20, c_893])).
% 4.61/1.81  tff(c_957, plain, (![A_256, B_257, C_258]: (u1_struct_0(k1_tsep_1(A_256, B_257, C_258))=k2_xboole_0(u1_struct_0(B_257), u1_struct_0(C_258)) | ~v1_pre_topc(k1_tsep_1(A_256, B_257, C_258)) | ~m1_pre_topc(C_258, A_256) | v2_struct_0(C_258) | ~m1_pre_topc(B_257, A_256) | v2_struct_0(B_257) | ~l1_pre_topc(A_256) | v2_struct_0(A_256))), inference(resolution, [status(thm)], [c_897, c_24])).
% 4.61/1.81  tff(c_961, plain, (![A_259, B_260, C_261]: (u1_struct_0(k1_tsep_1(A_259, B_260, C_261))=k2_xboole_0(u1_struct_0(B_260), u1_struct_0(C_261)) | ~m1_pre_topc(C_261, A_259) | v2_struct_0(C_261) | ~m1_pre_topc(B_260, A_259) | v2_struct_0(B_260) | ~l1_pre_topc(A_259) | v2_struct_0(A_259))), inference(resolution, [status(thm)], [c_22, c_957])).
% 4.61/1.81  tff(c_4, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.61/1.81  tff(c_1017, plain, (![A_262, C_263, A_264, B_265]: (r1_xboole_0(A_262, u1_struct_0(C_263)) | ~r1_xboole_0(A_262, u1_struct_0(k1_tsep_1(A_264, B_265, C_263))) | ~m1_pre_topc(C_263, A_264) | v2_struct_0(C_263) | ~m1_pre_topc(B_265, A_264) | v2_struct_0(B_265) | ~l1_pre_topc(A_264) | v2_struct_0(A_264))), inference(superposition, [status(thm), theory('equality')], [c_961, c_4])).
% 4.61/1.81  tff(c_1085, plain, (![A_278, C_279, A_280, B_281]: (r1_xboole_0(u1_struct_0(A_278), u1_struct_0(C_279)) | ~m1_pre_topc(C_279, A_280) | v2_struct_0(C_279) | ~m1_pre_topc(B_281, A_280) | v2_struct_0(B_281) | ~l1_pre_topc(A_280) | v2_struct_0(A_280) | ~r1_tsep_1(A_278, k1_tsep_1(A_280, B_281, C_279)) | ~l1_struct_0(k1_tsep_1(A_280, B_281, C_279)) | ~l1_struct_0(A_278))), inference(resolution, [status(thm)], [c_18, c_1017])).
% 4.61/1.81  tff(c_1087, plain, (r1_xboole_0(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_809, c_1085])).
% 4.61/1.81  tff(c_1090, plain, (r1_xboole_0(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_839, c_865, c_40, c_36, c_32, c_1087])).
% 4.61/1.81  tff(c_1091, plain, (r1_xboole_0(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_34, c_1090])).
% 4.61/1.81  tff(c_1094, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1091, c_16])).
% 4.61/1.81  tff(c_1097, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_839, c_1094])).
% 4.61/1.81  tff(c_1098, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_786, c_1097])).
% 4.61/1.81  tff(c_1101, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8, c_1098])).
% 4.61/1.81  tff(c_1105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_800, c_1101])).
% 4.61/1.81  tff(c_1107, plain, (~r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_808])).
% 4.61/1.81  tff(c_1106, plain, (r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_808])).
% 4.61/1.81  tff(c_1109, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1106])).
% 4.61/1.81  tff(c_1110, plain, (![B_285, A_286]: (r1_tsep_1(B_285, A_286) | ~r1_tsep_1(A_286, B_285) | ~l1_struct_0(B_285) | ~l1_struct_0(A_286))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.61/1.81  tff(c_1112, plain, (r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~l1_struct_0('#skF_4') | ~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_1109, c_1110])).
% 4.61/1.81  tff(c_1115, plain, (~l1_struct_0('#skF_4') | ~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1107, c_1112])).
% 4.61/1.81  tff(c_1116, plain, (~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1115])).
% 4.61/1.81  tff(c_1120, plain, (~l1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_1116])).
% 4.61/1.81  tff(c_1152, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1149, c_1120])).
% 4.61/1.81  tff(c_1155, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_32, c_1152])).
% 4.61/1.81  tff(c_1157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_34, c_1155])).
% 4.61/1.81  tff(c_1158, plain, (~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_1115])).
% 4.61/1.81  tff(c_1164, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8, c_1158])).
% 4.61/1.81  tff(c_1168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_803, c_1164])).
% 4.61/1.81  tff(c_1169, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_1106])).
% 4.61/1.81  tff(c_1171, plain, (![B_306, A_307]: (r1_tsep_1(B_306, A_307) | ~r1_tsep_1(A_307, B_306) | ~l1_struct_0(B_306) | ~l1_struct_0(A_307))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.61/1.81  tff(c_1173, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1169, c_1171])).
% 4.61/1.81  tff(c_1176, plain, (~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_786, c_1173])).
% 4.61/1.81  tff(c_1177, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1176])).
% 4.61/1.81  tff(c_1189, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8, c_1177])).
% 4.61/1.81  tff(c_1193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_800, c_1189])).
% 4.61/1.81  tff(c_1194, plain, (~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_1176])).
% 4.61/1.81  tff(c_1198, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8, c_1194])).
% 4.61/1.81  tff(c_1202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_803, c_1198])).
% 4.61/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.81  
% 4.61/1.81  Inference rules
% 4.61/1.81  ----------------------
% 4.61/1.81  #Ref     : 0
% 4.61/1.81  #Sup     : 239
% 4.61/1.81  #Fact    : 0
% 4.61/1.81  #Define  : 0
% 4.61/1.81  #Split   : 17
% 4.61/1.81  #Chain   : 0
% 4.61/1.81  #Close   : 0
% 4.61/1.81  
% 4.61/1.81  Ordering : KBO
% 4.61/1.81  
% 4.61/1.81  Simplification rules
% 4.61/1.81  ----------------------
% 4.61/1.81  #Subsume      : 34
% 4.61/1.81  #Demod        : 145
% 4.61/1.81  #Tautology    : 80
% 4.61/1.81  #SimpNegUnit  : 26
% 4.61/1.81  #BackRed      : 0
% 4.61/1.81  
% 4.61/1.81  #Partial instantiations: 0
% 4.61/1.81  #Strategies tried      : 1
% 4.61/1.81  
% 4.61/1.81  Timing (in seconds)
% 4.61/1.81  ----------------------
% 4.61/1.81  Preprocessing        : 0.35
% 4.61/1.81  Parsing              : 0.19
% 4.61/1.81  CNF conversion       : 0.03
% 4.61/1.81  Main loop            : 0.62
% 4.61/1.81  Inferencing          : 0.22
% 4.61/1.81  Reduction            : 0.15
% 4.61/1.81  Demodulation         : 0.10
% 4.61/1.81  BG Simplification    : 0.04
% 4.61/1.81  Subsumption          : 0.18
% 4.61/1.81  Abstraction          : 0.03
% 4.61/1.81  MUC search           : 0.00
% 4.61/1.81  Cooper               : 0.00
% 4.61/1.81  Total                : 1.03
% 4.61/1.81  Index Insertion      : 0.00
% 4.61/1.81  Index Deletion       : 0.00
% 4.61/1.81  Index Matching       : 0.00
% 4.61/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
