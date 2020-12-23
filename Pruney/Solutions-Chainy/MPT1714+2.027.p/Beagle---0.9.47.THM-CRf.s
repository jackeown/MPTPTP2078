%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:36 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 269 expanded)
%              Number of leaves         :   25 (  95 expanded)
%              Depth                    :   14
%              Number of atoms          :  238 (1081 expanded)
%              Number of equality atoms :    4 (   9 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_125,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_471,plain,(
    ! [B_103,A_104] :
      ( l1_pre_topc(B_103)
      | ~ m1_pre_topc(B_103,A_104)
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_483,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_471])).

tff(c_493,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_483])).

tff(c_10,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_477,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_471])).

tff(c_487,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_477])).

tff(c_406,plain,(
    ! [B_90,A_91] :
      ( l1_pre_topc(B_90)
      | ~ m1_pre_topc(B_90,A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_412,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_406])).

tff(c_422,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_412])).

tff(c_38,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_415,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_406])).

tff(c_425,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_415])).

tff(c_28,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_51,plain,(
    ! [B_36,A_37] :
      ( l1_pre_topc(B_36)
      | ~ m1_pre_topc(B_36,A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_60,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_51])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_60])).

tff(c_16,plain,(
    ! [A_10,B_12] :
      ( r1_xboole_0(u1_struct_0(A_10),u1_struct_0(B_12))
      | ~ r1_tsep_1(A_10,B_12)
      | ~ l1_struct_0(B_12)
      | ~ l1_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_131,plain,(
    ! [B_59,C_60,A_61] :
      ( r1_tarski(u1_struct_0(B_59),u1_struct_0(C_60))
      | ~ m1_pre_topc(B_59,C_60)
      | ~ m1_pre_topc(C_60,A_61)
      | ~ m1_pre_topc(B_59,A_61)
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_137,plain,(
    ! [B_59] :
      ( r1_tarski(u1_struct_0(B_59),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_59,'#skF_2')
      | ~ m1_pre_topc(B_59,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_131])).

tff(c_168,plain,(
    ! [B_64] :
      ( r1_tarski(u1_struct_0(B_64),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_64,'#skF_2')
      | ~ m1_pre_topc(B_64,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_137])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_213,plain,(
    ! [B_67] :
      ( k2_xboole_0(u1_struct_0(B_67),u1_struct_0('#skF_2')) = u1_struct_0('#skF_2')
      | ~ m1_pre_topc(B_67,'#skF_2')
      | ~ m1_pre_topc(B_67,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_168,c_2])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_xboole_0(A_3,B_4)
      | ~ r1_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_245,plain,(
    ! [A_72,B_73] :
      ( r1_xboole_0(A_72,u1_struct_0(B_73))
      | ~ r1_xboole_0(A_72,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_73,'#skF_2')
      | ~ m1_pre_topc(B_73,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_8])).

tff(c_249,plain,(
    ! [A_10,B_73] :
      ( r1_xboole_0(u1_struct_0(A_10),u1_struct_0(B_73))
      | ~ m1_pre_topc(B_73,'#skF_2')
      | ~ m1_pre_topc(B_73,'#skF_1')
      | ~ r1_tsep_1(A_10,'#skF_2')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_16,c_245])).

tff(c_273,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_276,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_273])).

tff(c_280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_276])).

tff(c_282,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_57,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_51])).

tff(c_67,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_57])).

tff(c_63,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_51])).

tff(c_73,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_63])).

tff(c_24,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_48,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_77,plain,(
    ! [B_44,A_45] :
      ( r1_tsep_1(B_44,A_45)
      | ~ r1_tsep_1(A_45,B_44)
      | ~ l1_struct_0(B_44)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_80,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_77])).

tff(c_81,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_93,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_81])).

tff(c_97,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_93])).

tff(c_98,plain,
    ( ~ l1_struct_0('#skF_4')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_100,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_103,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_100])).

tff(c_107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_103])).

tff(c_109,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_108,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_99,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_139,plain,(
    ! [B_59] :
      ( r1_tarski(u1_struct_0(B_59),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_59,'#skF_3')
      | ~ m1_pre_topc(B_59,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_131])).

tff(c_160,plain,(
    ! [B_63] :
      ( r1_tarski(u1_struct_0(B_63),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_63,'#skF_3')
      | ~ m1_pre_topc(B_63,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_139])).

tff(c_195,plain,(
    ! [B_66] :
      ( k2_xboole_0(u1_struct_0(B_66),u1_struct_0('#skF_3')) = u1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_66,'#skF_3')
      | ~ m1_pre_topc(B_66,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_160,c_2])).

tff(c_231,plain,(
    ! [A_68,B_69] :
      ( r1_xboole_0(A_68,u1_struct_0(B_69))
      | ~ r1_xboole_0(A_68,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_69,'#skF_3')
      | ~ m1_pre_topc(B_69,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_8])).

tff(c_234,plain,(
    ! [A_10,B_69] :
      ( r1_xboole_0(u1_struct_0(A_10),u1_struct_0(B_69))
      | ~ m1_pre_topc(B_69,'#skF_3')
      | ~ m1_pre_topc(B_69,'#skF_1')
      | ~ r1_tsep_1(A_10,'#skF_3')
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_16,c_231])).

tff(c_306,plain,(
    ! [A_78,B_79] :
      ( r1_xboole_0(u1_struct_0(A_78),u1_struct_0(B_79))
      | ~ m1_pre_topc(B_79,'#skF_3')
      | ~ m1_pre_topc(B_79,'#skF_1')
      | ~ r1_tsep_1(A_78,'#skF_3')
      | ~ l1_struct_0(A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_234])).

tff(c_14,plain,(
    ! [A_10,B_12] :
      ( r1_tsep_1(A_10,B_12)
      | ~ r1_xboole_0(u1_struct_0(A_10),u1_struct_0(B_12))
      | ~ l1_struct_0(B_12)
      | ~ l1_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_335,plain,(
    ! [A_82,B_83] :
      ( r1_tsep_1(A_82,B_83)
      | ~ l1_struct_0(B_83)
      | ~ m1_pre_topc(B_83,'#skF_3')
      | ~ m1_pre_topc(B_83,'#skF_1')
      | ~ r1_tsep_1(A_82,'#skF_3')
      | ~ l1_struct_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_306,c_14])).

tff(c_337,plain,(
    ! [B_83] :
      ( r1_tsep_1('#skF_4',B_83)
      | ~ l1_struct_0(B_83)
      | ~ m1_pre_topc(B_83,'#skF_3')
      | ~ m1_pre_topc(B_83,'#skF_1')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_108,c_335])).

tff(c_359,plain,(
    ! [B_85] :
      ( r1_tsep_1('#skF_4',B_85)
      | ~ l1_struct_0(B_85)
      | ~ m1_pre_topc(B_85,'#skF_3')
      | ~ m1_pre_topc(B_85,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_337])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( r1_tsep_1(B_14,A_13)
      | ~ r1_tsep_1(A_13,B_14)
      | ~ l1_struct_0(B_14)
      | ~ l1_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_367,plain,(
    ! [B_85] :
      ( r1_tsep_1(B_85,'#skF_4')
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0(B_85)
      | ~ m1_pre_topc(B_85,'#skF_3')
      | ~ m1_pre_topc(B_85,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_359,c_18])).

tff(c_387,plain,(
    ! [B_87] :
      ( r1_tsep_1(B_87,'#skF_4')
      | ~ l1_struct_0(B_87)
      | ~ m1_pre_topc(B_87,'#skF_3')
      | ~ m1_pre_topc(B_87,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_367])).

tff(c_26,plain,
    ( ~ r1_tsep_1('#skF_4','#skF_2')
    | ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_49,plain,(
    ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_394,plain,
    ( ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_387,c_49])).

tff(c_402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28,c_282,c_394])).

tff(c_403,plain,(
    ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_404,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_433,plain,(
    ! [B_98,A_99] :
      ( r1_tsep_1(B_98,A_99)
      | ~ r1_tsep_1(A_99,B_98)
      | ~ l1_struct_0(B_98)
      | ~ l1_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_435,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_404,c_433])).

tff(c_440,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_435])).

tff(c_442,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_440])).

tff(c_445,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_442])).

tff(c_449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_445])).

tff(c_450,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_440])).

tff(c_463,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_450])).

tff(c_467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_463])).

tff(c_469,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_468,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_499,plain,(
    ! [B_113,A_114] :
      ( r1_tsep_1(B_113,A_114)
      | ~ r1_tsep_1(A_114,B_113)
      | ~ l1_struct_0(B_113)
      | ~ l1_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_501,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_468,c_499])).

tff(c_504,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_469,c_501])).

tff(c_505,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_504])).

tff(c_508,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_505])).

tff(c_512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_508])).

tff(c_513,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_504])).

tff(c_517,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_513])).

tff(c_521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_517])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:24:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.34  
% 2.64/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.34  %$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.64/1.34  
% 2.64/1.34  %Foreground sorts:
% 2.64/1.34  
% 2.64/1.34  
% 2.64/1.34  %Background operators:
% 2.64/1.34  
% 2.64/1.34  
% 2.64/1.34  %Foreground operators:
% 2.64/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.64/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.64/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.64/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.64/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.64/1.34  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.64/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.64/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.34  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.64/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.64/1.34  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.64/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.64/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.64/1.34  
% 2.64/1.36  tff(f_125, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tmap_1)).
% 2.64/1.36  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.64/1.36  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.64/1.36  tff(f_65, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.64/1.36  tff(f_87, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.64/1.36  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.64/1.36  tff(f_45, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.64/1.36  tff(f_73, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.64/1.36  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.64/1.36  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.64/1.36  tff(c_471, plain, (![B_103, A_104]: (l1_pre_topc(B_103) | ~m1_pre_topc(B_103, A_104) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.64/1.36  tff(c_483, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_471])).
% 2.64/1.36  tff(c_493, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_483])).
% 2.64/1.36  tff(c_10, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.64/1.36  tff(c_30, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.64/1.36  tff(c_477, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_471])).
% 2.64/1.36  tff(c_487, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_477])).
% 2.64/1.36  tff(c_406, plain, (![B_90, A_91]: (l1_pre_topc(B_90) | ~m1_pre_topc(B_90, A_91) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.64/1.36  tff(c_412, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_406])).
% 2.64/1.36  tff(c_422, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_412])).
% 2.64/1.36  tff(c_38, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.64/1.36  tff(c_415, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_406])).
% 2.64/1.36  tff(c_425, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_415])).
% 2.64/1.36  tff(c_28, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.64/1.36  tff(c_51, plain, (![B_36, A_37]: (l1_pre_topc(B_36) | ~m1_pre_topc(B_36, A_37) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.64/1.36  tff(c_60, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_51])).
% 2.64/1.36  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_60])).
% 2.64/1.36  tff(c_16, plain, (![A_10, B_12]: (r1_xboole_0(u1_struct_0(A_10), u1_struct_0(B_12)) | ~r1_tsep_1(A_10, B_12) | ~l1_struct_0(B_12) | ~l1_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.64/1.36  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.64/1.36  tff(c_131, plain, (![B_59, C_60, A_61]: (r1_tarski(u1_struct_0(B_59), u1_struct_0(C_60)) | ~m1_pre_topc(B_59, C_60) | ~m1_pre_topc(C_60, A_61) | ~m1_pre_topc(B_59, A_61) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.64/1.36  tff(c_137, plain, (![B_59]: (r1_tarski(u1_struct_0(B_59), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_59, '#skF_2') | ~m1_pre_topc(B_59, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_131])).
% 2.64/1.36  tff(c_168, plain, (![B_64]: (r1_tarski(u1_struct_0(B_64), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_64, '#skF_2') | ~m1_pre_topc(B_64, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_137])).
% 2.64/1.36  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.64/1.36  tff(c_213, plain, (![B_67]: (k2_xboole_0(u1_struct_0(B_67), u1_struct_0('#skF_2'))=u1_struct_0('#skF_2') | ~m1_pre_topc(B_67, '#skF_2') | ~m1_pre_topc(B_67, '#skF_1'))), inference(resolution, [status(thm)], [c_168, c_2])).
% 2.64/1.36  tff(c_8, plain, (![A_3, B_4, C_5]: (r1_xboole_0(A_3, B_4) | ~r1_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.64/1.36  tff(c_245, plain, (![A_72, B_73]: (r1_xboole_0(A_72, u1_struct_0(B_73)) | ~r1_xboole_0(A_72, u1_struct_0('#skF_2')) | ~m1_pre_topc(B_73, '#skF_2') | ~m1_pre_topc(B_73, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_213, c_8])).
% 2.64/1.36  tff(c_249, plain, (![A_10, B_73]: (r1_xboole_0(u1_struct_0(A_10), u1_struct_0(B_73)) | ~m1_pre_topc(B_73, '#skF_2') | ~m1_pre_topc(B_73, '#skF_1') | ~r1_tsep_1(A_10, '#skF_2') | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_10))), inference(resolution, [status(thm)], [c_16, c_245])).
% 2.64/1.36  tff(c_273, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_249])).
% 2.64/1.36  tff(c_276, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_273])).
% 2.64/1.36  tff(c_280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_276])).
% 2.64/1.36  tff(c_282, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_249])).
% 2.64/1.36  tff(c_57, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_51])).
% 2.64/1.36  tff(c_67, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_57])).
% 2.64/1.36  tff(c_63, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_51])).
% 2.64/1.36  tff(c_73, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_63])).
% 2.64/1.36  tff(c_24, plain, (r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.64/1.36  tff(c_48, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_24])).
% 2.64/1.36  tff(c_77, plain, (![B_44, A_45]: (r1_tsep_1(B_44, A_45) | ~r1_tsep_1(A_45, B_44) | ~l1_struct_0(B_44) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.64/1.36  tff(c_80, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_77])).
% 2.64/1.36  tff(c_81, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_80])).
% 2.64/1.36  tff(c_93, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_10, c_81])).
% 2.64/1.36  tff(c_97, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_93])).
% 2.64/1.36  tff(c_98, plain, (~l1_struct_0('#skF_4') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_80])).
% 2.64/1.36  tff(c_100, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_98])).
% 2.64/1.36  tff(c_103, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_10, c_100])).
% 2.64/1.36  tff(c_107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_103])).
% 2.64/1.36  tff(c_109, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_98])).
% 2.64/1.36  tff(c_108, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_98])).
% 2.64/1.36  tff(c_99, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_80])).
% 2.64/1.36  tff(c_139, plain, (![B_59]: (r1_tarski(u1_struct_0(B_59), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_59, '#skF_3') | ~m1_pre_topc(B_59, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_131])).
% 2.64/1.36  tff(c_160, plain, (![B_63]: (r1_tarski(u1_struct_0(B_63), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_63, '#skF_3') | ~m1_pre_topc(B_63, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_139])).
% 2.64/1.36  tff(c_195, plain, (![B_66]: (k2_xboole_0(u1_struct_0(B_66), u1_struct_0('#skF_3'))=u1_struct_0('#skF_3') | ~m1_pre_topc(B_66, '#skF_3') | ~m1_pre_topc(B_66, '#skF_1'))), inference(resolution, [status(thm)], [c_160, c_2])).
% 2.64/1.36  tff(c_231, plain, (![A_68, B_69]: (r1_xboole_0(A_68, u1_struct_0(B_69)) | ~r1_xboole_0(A_68, u1_struct_0('#skF_3')) | ~m1_pre_topc(B_69, '#skF_3') | ~m1_pre_topc(B_69, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_195, c_8])).
% 2.64/1.36  tff(c_234, plain, (![A_10, B_69]: (r1_xboole_0(u1_struct_0(A_10), u1_struct_0(B_69)) | ~m1_pre_topc(B_69, '#skF_3') | ~m1_pre_topc(B_69, '#skF_1') | ~r1_tsep_1(A_10, '#skF_3') | ~l1_struct_0('#skF_3') | ~l1_struct_0(A_10))), inference(resolution, [status(thm)], [c_16, c_231])).
% 2.64/1.36  tff(c_306, plain, (![A_78, B_79]: (r1_xboole_0(u1_struct_0(A_78), u1_struct_0(B_79)) | ~m1_pre_topc(B_79, '#skF_3') | ~m1_pre_topc(B_79, '#skF_1') | ~r1_tsep_1(A_78, '#skF_3') | ~l1_struct_0(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_234])).
% 2.64/1.36  tff(c_14, plain, (![A_10, B_12]: (r1_tsep_1(A_10, B_12) | ~r1_xboole_0(u1_struct_0(A_10), u1_struct_0(B_12)) | ~l1_struct_0(B_12) | ~l1_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.64/1.36  tff(c_335, plain, (![A_82, B_83]: (r1_tsep_1(A_82, B_83) | ~l1_struct_0(B_83) | ~m1_pre_topc(B_83, '#skF_3') | ~m1_pre_topc(B_83, '#skF_1') | ~r1_tsep_1(A_82, '#skF_3') | ~l1_struct_0(A_82))), inference(resolution, [status(thm)], [c_306, c_14])).
% 2.64/1.36  tff(c_337, plain, (![B_83]: (r1_tsep_1('#skF_4', B_83) | ~l1_struct_0(B_83) | ~m1_pre_topc(B_83, '#skF_3') | ~m1_pre_topc(B_83, '#skF_1') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_108, c_335])).
% 2.64/1.36  tff(c_359, plain, (![B_85]: (r1_tsep_1('#skF_4', B_85) | ~l1_struct_0(B_85) | ~m1_pre_topc(B_85, '#skF_3') | ~m1_pre_topc(B_85, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_337])).
% 2.64/1.36  tff(c_18, plain, (![B_14, A_13]: (r1_tsep_1(B_14, A_13) | ~r1_tsep_1(A_13, B_14) | ~l1_struct_0(B_14) | ~l1_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.64/1.36  tff(c_367, plain, (![B_85]: (r1_tsep_1(B_85, '#skF_4') | ~l1_struct_0('#skF_4') | ~l1_struct_0(B_85) | ~m1_pre_topc(B_85, '#skF_3') | ~m1_pre_topc(B_85, '#skF_1'))), inference(resolution, [status(thm)], [c_359, c_18])).
% 2.64/1.36  tff(c_387, plain, (![B_87]: (r1_tsep_1(B_87, '#skF_4') | ~l1_struct_0(B_87) | ~m1_pre_topc(B_87, '#skF_3') | ~m1_pre_topc(B_87, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_367])).
% 2.64/1.36  tff(c_26, plain, (~r1_tsep_1('#skF_4', '#skF_2') | ~r1_tsep_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.64/1.36  tff(c_49, plain, (~r1_tsep_1('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_26])).
% 2.64/1.36  tff(c_394, plain, (~l1_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_387, c_49])).
% 2.64/1.36  tff(c_402, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_28, c_282, c_394])).
% 2.64/1.36  tff(c_403, plain, (~r1_tsep_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_26])).
% 2.64/1.36  tff(c_404, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_26])).
% 2.64/1.36  tff(c_433, plain, (![B_98, A_99]: (r1_tsep_1(B_98, A_99) | ~r1_tsep_1(A_99, B_98) | ~l1_struct_0(B_98) | ~l1_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.64/1.36  tff(c_435, plain, (r1_tsep_1('#skF_4', '#skF_2') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_404, c_433])).
% 2.64/1.36  tff(c_440, plain, (~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_403, c_435])).
% 2.64/1.36  tff(c_442, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_440])).
% 2.64/1.36  tff(c_445, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_442])).
% 2.64/1.36  tff(c_449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_425, c_445])).
% 2.64/1.36  tff(c_450, plain, (~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_440])).
% 2.64/1.36  tff(c_463, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_10, c_450])).
% 2.64/1.36  tff(c_467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_422, c_463])).
% 2.64/1.36  tff(c_469, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_24])).
% 2.64/1.36  tff(c_468, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_24])).
% 2.64/1.36  tff(c_499, plain, (![B_113, A_114]: (r1_tsep_1(B_113, A_114) | ~r1_tsep_1(A_114, B_113) | ~l1_struct_0(B_113) | ~l1_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.64/1.36  tff(c_501, plain, (r1_tsep_1('#skF_3', '#skF_4') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_468, c_499])).
% 2.64/1.36  tff(c_504, plain, (~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_469, c_501])).
% 2.64/1.36  tff(c_505, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_504])).
% 2.64/1.36  tff(c_508, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_10, c_505])).
% 2.64/1.36  tff(c_512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_487, c_508])).
% 2.64/1.36  tff(c_513, plain, (~l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_504])).
% 2.64/1.36  tff(c_517, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_10, c_513])).
% 2.64/1.36  tff(c_521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_493, c_517])).
% 2.64/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.36  
% 2.64/1.36  Inference rules
% 2.64/1.36  ----------------------
% 2.64/1.36  #Ref     : 0
% 2.64/1.36  #Sup     : 84
% 2.64/1.36  #Fact    : 0
% 2.64/1.36  #Define  : 0
% 2.64/1.36  #Split   : 10
% 2.64/1.36  #Chain   : 0
% 2.64/1.36  #Close   : 0
% 2.64/1.36  
% 2.64/1.36  Ordering : KBO
% 2.64/1.36  
% 2.64/1.36  Simplification rules
% 2.64/1.36  ----------------------
% 2.64/1.36  #Subsume      : 7
% 2.64/1.36  #Demod        : 62
% 2.64/1.36  #Tautology    : 26
% 2.64/1.36  #SimpNegUnit  : 2
% 2.64/1.36  #BackRed      : 0
% 2.64/1.36  
% 2.64/1.36  #Partial instantiations: 0
% 2.64/1.36  #Strategies tried      : 1
% 2.64/1.36  
% 2.64/1.36  Timing (in seconds)
% 2.64/1.36  ----------------------
% 2.82/1.37  Preprocessing        : 0.30
% 2.82/1.37  Parsing              : 0.17
% 2.82/1.37  CNF conversion       : 0.02
% 2.82/1.37  Main loop            : 0.29
% 2.82/1.37  Inferencing          : 0.11
% 2.82/1.37  Reduction            : 0.08
% 2.82/1.37  Demodulation         : 0.05
% 2.82/1.37  BG Simplification    : 0.02
% 2.82/1.37  Subsumption          : 0.06
% 2.82/1.37  Abstraction          : 0.01
% 2.82/1.37  MUC search           : 0.00
% 2.82/1.37  Cooper               : 0.00
% 2.82/1.37  Total                : 0.63
% 2.82/1.37  Index Insertion      : 0.00
% 2.82/1.37  Index Deletion       : 0.00
% 2.82/1.37  Index Matching       : 0.00
% 2.82/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
