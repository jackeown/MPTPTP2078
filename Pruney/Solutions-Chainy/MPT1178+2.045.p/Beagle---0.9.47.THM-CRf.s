%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:08 EST 2020

% Result     : Theorem 6.05s
% Output     : CNFRefutation 6.40s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 139 expanded)
%              Number of leaves         :   33 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  199 ( 435 expanded)
%              Number of equality atoms :    7 (  36 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => k3_tarski(k4_orders_2(A,B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( C = k4_orders_2(A,B)
            <=> ! [D] :
                  ( r2_hidden(D,C)
                <=> m2_orders_2(D,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k3_tarski(A),B)
        & r2_hidden(C,A) )
     => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

tff(f_104,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => r2_hidden(k1_funct_1(B,u1_struct_0(A)),C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_44,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_42,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_40,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_38,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_36,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_114,plain,(
    ! [A_65,B_66] :
      ( m2_orders_2('#skF_4'(A_65,B_66),A_65,B_66)
      | ~ m1_orders_1(B_66,k1_orders_1(u1_struct_0(A_65)))
      | ~ l1_orders_2(A_65)
      | ~ v5_orders_2(A_65)
      | ~ v4_orders_2(A_65)
      | ~ v3_orders_2(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_116,plain,
    ( m2_orders_2('#skF_4'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_114])).

tff(c_119,plain,
    ( m2_orders_2('#skF_4'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_116])).

tff(c_120,plain,(
    m2_orders_2('#skF_4'('#skF_5','#skF_6'),'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_119])).

tff(c_10,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_73,plain,(
    ! [A_48,B_49] : ~ r2_hidden(A_48,k2_zfmisc_1(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_76,plain,(
    ! [A_6] : ~ r2_hidden(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_73])).

tff(c_93,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_1'(A_55,B_56),A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_102,plain,(
    ! [A_55] : r1_tarski(A_55,A_55) ),
    inference(resolution,[status(thm)],[c_93,c_4])).

tff(c_34,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_104,plain,(
    ! [C_57,B_58,A_59] :
      ( r2_hidden(C_57,B_58)
      | ~ r2_hidden(C_57,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_107,plain,(
    ! [A_1,B_2,B_58] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_58)
      | ~ r1_tarski(A_1,B_58)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_104])).

tff(c_173,plain,(
    ! [D_78,A_79,B_80] :
      ( m2_orders_2(D_78,A_79,B_80)
      | ~ r2_hidden(D_78,k4_orders_2(A_79,B_80))
      | ~ m1_orders_1(B_80,k1_orders_1(u1_struct_0(A_79)))
      | ~ l1_orders_2(A_79)
      | ~ v5_orders_2(A_79)
      | ~ v4_orders_2(A_79)
      | ~ v3_orders_2(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3310,plain,(
    ! [A_337,B_338,A_339,B_340] :
      ( m2_orders_2('#skF_1'(A_337,B_338),A_339,B_340)
      | ~ m1_orders_1(B_340,k1_orders_1(u1_struct_0(A_339)))
      | ~ l1_orders_2(A_339)
      | ~ v5_orders_2(A_339)
      | ~ v4_orders_2(A_339)
      | ~ v3_orders_2(A_339)
      | v2_struct_0(A_339)
      | ~ r1_tarski(A_337,k4_orders_2(A_339,B_340))
      | r1_tarski(A_337,B_338) ) ),
    inference(resolution,[status(thm)],[c_107,c_173])).

tff(c_3312,plain,(
    ! [A_337,B_338] :
      ( m2_orders_2('#skF_1'(A_337,B_338),'#skF_5','#skF_6')
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r1_tarski(A_337,k4_orders_2('#skF_5','#skF_6'))
      | r1_tarski(A_337,B_338) ) ),
    inference(resolution,[status(thm)],[c_36,c_3310])).

tff(c_3315,plain,(
    ! [A_337,B_338] :
      ( m2_orders_2('#skF_1'(A_337,B_338),'#skF_5','#skF_6')
      | v2_struct_0('#skF_5')
      | ~ r1_tarski(A_337,k4_orders_2('#skF_5','#skF_6'))
      | r1_tarski(A_337,B_338) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_3312])).

tff(c_3316,plain,(
    ! [A_337,B_338] :
      ( m2_orders_2('#skF_1'(A_337,B_338),'#skF_5','#skF_6')
      | ~ r1_tarski(A_337,k4_orders_2('#skF_5','#skF_6'))
      | r1_tarski(A_337,B_338) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3315])).

tff(c_110,plain,(
    ! [C_62,B_63,A_64] :
      ( r1_tarski(C_62,B_63)
      | ~ r2_hidden(C_62,A_64)
      | ~ r1_tarski(k3_tarski(A_64),B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_164,plain,(
    ! [A_75,B_76,B_77] :
      ( r1_tarski('#skF_1'(A_75,B_76),B_77)
      | ~ r1_tarski(k3_tarski(A_75),B_77)
      | r1_tarski(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_6,c_110])).

tff(c_170,plain,(
    ! [A_75,B_76] :
      ( r1_tarski('#skF_1'(A_75,B_76),k3_tarski(A_75))
      | r1_tarski(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_102,c_164])).

tff(c_245,plain,(
    ! [B_95,A_96,C_97] :
      ( r2_hidden(k1_funct_1(B_95,u1_struct_0(A_96)),C_97)
      | ~ m2_orders_2(C_97,A_96,B_95)
      | ~ m1_orders_1(B_95,k1_orders_1(u1_struct_0(A_96)))
      | ~ l1_orders_2(A_96)
      | ~ v5_orders_2(A_96)
      | ~ v4_orders_2(A_96)
      | ~ v3_orders_2(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1208,plain,(
    ! [B_217,A_218,B_219,C_220] :
      ( r2_hidden(k1_funct_1(B_217,u1_struct_0(A_218)),B_219)
      | ~ r1_tarski(C_220,B_219)
      | ~ m2_orders_2(C_220,A_218,B_217)
      | ~ m1_orders_1(B_217,k1_orders_1(u1_struct_0(A_218)))
      | ~ l1_orders_2(A_218)
      | ~ v5_orders_2(A_218)
      | ~ v4_orders_2(A_218)
      | ~ v3_orders_2(A_218)
      | v2_struct_0(A_218) ) ),
    inference(resolution,[status(thm)],[c_245,c_2])).

tff(c_4103,plain,(
    ! [B_391,A_392,A_393,B_394] :
      ( r2_hidden(k1_funct_1(B_391,u1_struct_0(A_392)),k3_tarski(A_393))
      | ~ m2_orders_2('#skF_1'(A_393,B_394),A_392,B_391)
      | ~ m1_orders_1(B_391,k1_orders_1(u1_struct_0(A_392)))
      | ~ l1_orders_2(A_392)
      | ~ v5_orders_2(A_392)
      | ~ v4_orders_2(A_392)
      | ~ v3_orders_2(A_392)
      | v2_struct_0(A_392)
      | r1_tarski(A_393,B_394) ) ),
    inference(resolution,[status(thm)],[c_170,c_1208])).

tff(c_4105,plain,(
    ! [A_337,B_338] :
      ( r2_hidden(k1_funct_1('#skF_6',u1_struct_0('#skF_5')),k3_tarski(A_337))
      | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r1_tarski(A_337,k4_orders_2('#skF_5','#skF_6'))
      | r1_tarski(A_337,B_338) ) ),
    inference(resolution,[status(thm)],[c_3316,c_4103])).

tff(c_4110,plain,(
    ! [A_337,B_338] :
      ( r2_hidden(k1_funct_1('#skF_6',u1_struct_0('#skF_5')),k3_tarski(A_337))
      | v2_struct_0('#skF_5')
      | ~ r1_tarski(A_337,k4_orders_2('#skF_5','#skF_6'))
      | r1_tarski(A_337,B_338) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_4105])).

tff(c_4113,plain,(
    ! [A_395,B_396] :
      ( r2_hidden(k1_funct_1('#skF_6',u1_struct_0('#skF_5')),k3_tarski(A_395))
      | ~ r1_tarski(A_395,k4_orders_2('#skF_5','#skF_6'))
      | r1_tarski(A_395,B_396) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4110])).

tff(c_196,plain,(
    ! [D_85,A_86,B_87] :
      ( r2_hidden(D_85,k4_orders_2(A_86,B_87))
      | ~ m2_orders_2(D_85,A_86,B_87)
      | ~ m1_orders_1(B_87,k1_orders_1(u1_struct_0(A_86)))
      | ~ l1_orders_2(A_86)
      | ~ v5_orders_2(A_86)
      | ~ v4_orders_2(A_86)
      | ~ v3_orders_2(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_198,plain,(
    ! [D_85] :
      ( r2_hidden(D_85,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_85,'#skF_5','#skF_6')
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_196])).

tff(c_201,plain,(
    ! [D_85] :
      ( r2_hidden(D_85,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_85,'#skF_5','#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_198])).

tff(c_203,plain,(
    ! [D_88] :
      ( r2_hidden(D_88,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_88,'#skF_5','#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_201])).

tff(c_221,plain,(
    ! [D_88,B_2] :
      ( r2_hidden(D_88,B_2)
      | ~ r1_tarski(k4_orders_2('#skF_5','#skF_6'),B_2)
      | ~ m2_orders_2(D_88,'#skF_5','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_203,c_2])).

tff(c_4194,plain,(
    ! [D_88,B_396] :
      ( r2_hidden(D_88,B_396)
      | ~ m2_orders_2(D_88,'#skF_5','#skF_6')
      | r2_hidden(k1_funct_1('#skF_6',u1_struct_0('#skF_5')),k3_tarski(k4_orders_2('#skF_5','#skF_6')))
      | ~ r1_tarski(k4_orders_2('#skF_5','#skF_6'),k4_orders_2('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_4113,c_221])).

tff(c_4233,plain,(
    ! [D_88,B_396] :
      ( r2_hidden(D_88,B_396)
      | ~ m2_orders_2(D_88,'#skF_5','#skF_6')
      | r2_hidden(k1_funct_1('#skF_6',u1_struct_0('#skF_5')),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_34,c_4194])).

tff(c_4333,plain,(
    ! [D_398,B_399] :
      ( r2_hidden(D_398,B_399)
      | ~ m2_orders_2(D_398,'#skF_5','#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4233])).

tff(c_4413,plain,(
    ! [B_403] : r2_hidden('#skF_4'('#skF_5','#skF_6'),B_403) ),
    inference(resolution,[status(thm)],[c_120,c_4333])).

tff(c_4433,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_4413,c_76])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n011.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 17:29:27 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.05/2.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.05/2.24  
% 6.05/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.05/2.24  %$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.05/2.24  
% 6.05/2.24  %Foreground sorts:
% 6.05/2.24  
% 6.05/2.24  
% 6.05/2.24  %Background operators:
% 6.05/2.24  
% 6.05/2.24  
% 6.05/2.24  %Foreground operators:
% 6.05/2.24  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 6.05/2.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.05/2.24  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.05/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.05/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.05/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.05/2.24  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 6.05/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.05/2.24  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 6.05/2.24  tff('#skF_5', type, '#skF_5': $i).
% 6.05/2.24  tff('#skF_6', type, '#skF_6': $i).
% 6.05/2.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.05/2.24  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.05/2.24  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 6.05/2.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.05/2.24  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.05/2.24  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 6.05/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.05/2.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.05/2.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.05/2.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.05/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.05/2.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.05/2.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.05/2.24  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.05/2.24  
% 6.40/2.25  tff(f_122, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 6.40/2.25  tff(f_85, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 6.40/2.25  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.40/2.25  tff(f_41, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 6.40/2.25  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.40/2.25  tff(f_69, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 6.40/2.25  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_setfam_1)).
% 6.40/2.25  tff(f_104, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 6.40/2.25  tff(c_46, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.40/2.25  tff(c_44, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.40/2.25  tff(c_42, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.40/2.25  tff(c_40, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.40/2.25  tff(c_38, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.40/2.25  tff(c_36, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.40/2.25  tff(c_114, plain, (![A_65, B_66]: (m2_orders_2('#skF_4'(A_65, B_66), A_65, B_66) | ~m1_orders_1(B_66, k1_orders_1(u1_struct_0(A_65))) | ~l1_orders_2(A_65) | ~v5_orders_2(A_65) | ~v4_orders_2(A_65) | ~v3_orders_2(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.40/2.25  tff(c_116, plain, (m2_orders_2('#skF_4'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_36, c_114])).
% 6.40/2.25  tff(c_119, plain, (m2_orders_2('#skF_4'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_116])).
% 6.40/2.25  tff(c_120, plain, (m2_orders_2('#skF_4'('#skF_5', '#skF_6'), '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_46, c_119])).
% 6.40/2.25  tff(c_10, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.40/2.25  tff(c_73, plain, (![A_48, B_49]: (~r2_hidden(A_48, k2_zfmisc_1(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.40/2.25  tff(c_76, plain, (![A_6]: (~r2_hidden(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_73])).
% 6.40/2.25  tff(c_93, plain, (![A_55, B_56]: (r2_hidden('#skF_1'(A_55, B_56), A_55) | r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.40/2.25  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.40/2.25  tff(c_102, plain, (![A_55]: (r1_tarski(A_55, A_55))), inference(resolution, [status(thm)], [c_93, c_4])).
% 6.40/2.25  tff(c_34, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.40/2.25  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.40/2.25  tff(c_104, plain, (![C_57, B_58, A_59]: (r2_hidden(C_57, B_58) | ~r2_hidden(C_57, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.40/2.25  tff(c_107, plain, (![A_1, B_2, B_58]: (r2_hidden('#skF_1'(A_1, B_2), B_58) | ~r1_tarski(A_1, B_58) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_104])).
% 6.40/2.25  tff(c_173, plain, (![D_78, A_79, B_80]: (m2_orders_2(D_78, A_79, B_80) | ~r2_hidden(D_78, k4_orders_2(A_79, B_80)) | ~m1_orders_1(B_80, k1_orders_1(u1_struct_0(A_79))) | ~l1_orders_2(A_79) | ~v5_orders_2(A_79) | ~v4_orders_2(A_79) | ~v3_orders_2(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.40/2.25  tff(c_3310, plain, (![A_337, B_338, A_339, B_340]: (m2_orders_2('#skF_1'(A_337, B_338), A_339, B_340) | ~m1_orders_1(B_340, k1_orders_1(u1_struct_0(A_339))) | ~l1_orders_2(A_339) | ~v5_orders_2(A_339) | ~v4_orders_2(A_339) | ~v3_orders_2(A_339) | v2_struct_0(A_339) | ~r1_tarski(A_337, k4_orders_2(A_339, B_340)) | r1_tarski(A_337, B_338))), inference(resolution, [status(thm)], [c_107, c_173])).
% 6.40/2.25  tff(c_3312, plain, (![A_337, B_338]: (m2_orders_2('#skF_1'(A_337, B_338), '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r1_tarski(A_337, k4_orders_2('#skF_5', '#skF_6')) | r1_tarski(A_337, B_338))), inference(resolution, [status(thm)], [c_36, c_3310])).
% 6.40/2.25  tff(c_3315, plain, (![A_337, B_338]: (m2_orders_2('#skF_1'(A_337, B_338), '#skF_5', '#skF_6') | v2_struct_0('#skF_5') | ~r1_tarski(A_337, k4_orders_2('#skF_5', '#skF_6')) | r1_tarski(A_337, B_338))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_3312])).
% 6.40/2.25  tff(c_3316, plain, (![A_337, B_338]: (m2_orders_2('#skF_1'(A_337, B_338), '#skF_5', '#skF_6') | ~r1_tarski(A_337, k4_orders_2('#skF_5', '#skF_6')) | r1_tarski(A_337, B_338))), inference(negUnitSimplification, [status(thm)], [c_46, c_3315])).
% 6.40/2.25  tff(c_110, plain, (![C_62, B_63, A_64]: (r1_tarski(C_62, B_63) | ~r2_hidden(C_62, A_64) | ~r1_tarski(k3_tarski(A_64), B_63))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.40/2.25  tff(c_164, plain, (![A_75, B_76, B_77]: (r1_tarski('#skF_1'(A_75, B_76), B_77) | ~r1_tarski(k3_tarski(A_75), B_77) | r1_tarski(A_75, B_76))), inference(resolution, [status(thm)], [c_6, c_110])).
% 6.40/2.25  tff(c_170, plain, (![A_75, B_76]: (r1_tarski('#skF_1'(A_75, B_76), k3_tarski(A_75)) | r1_tarski(A_75, B_76))), inference(resolution, [status(thm)], [c_102, c_164])).
% 6.40/2.25  tff(c_245, plain, (![B_95, A_96, C_97]: (r2_hidden(k1_funct_1(B_95, u1_struct_0(A_96)), C_97) | ~m2_orders_2(C_97, A_96, B_95) | ~m1_orders_1(B_95, k1_orders_1(u1_struct_0(A_96))) | ~l1_orders_2(A_96) | ~v5_orders_2(A_96) | ~v4_orders_2(A_96) | ~v3_orders_2(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.40/2.25  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.40/2.25  tff(c_1208, plain, (![B_217, A_218, B_219, C_220]: (r2_hidden(k1_funct_1(B_217, u1_struct_0(A_218)), B_219) | ~r1_tarski(C_220, B_219) | ~m2_orders_2(C_220, A_218, B_217) | ~m1_orders_1(B_217, k1_orders_1(u1_struct_0(A_218))) | ~l1_orders_2(A_218) | ~v5_orders_2(A_218) | ~v4_orders_2(A_218) | ~v3_orders_2(A_218) | v2_struct_0(A_218))), inference(resolution, [status(thm)], [c_245, c_2])).
% 6.40/2.25  tff(c_4103, plain, (![B_391, A_392, A_393, B_394]: (r2_hidden(k1_funct_1(B_391, u1_struct_0(A_392)), k3_tarski(A_393)) | ~m2_orders_2('#skF_1'(A_393, B_394), A_392, B_391) | ~m1_orders_1(B_391, k1_orders_1(u1_struct_0(A_392))) | ~l1_orders_2(A_392) | ~v5_orders_2(A_392) | ~v4_orders_2(A_392) | ~v3_orders_2(A_392) | v2_struct_0(A_392) | r1_tarski(A_393, B_394))), inference(resolution, [status(thm)], [c_170, c_1208])).
% 6.40/2.25  tff(c_4105, plain, (![A_337, B_338]: (r2_hidden(k1_funct_1('#skF_6', u1_struct_0('#skF_5')), k3_tarski(A_337)) | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r1_tarski(A_337, k4_orders_2('#skF_5', '#skF_6')) | r1_tarski(A_337, B_338))), inference(resolution, [status(thm)], [c_3316, c_4103])).
% 6.40/2.25  tff(c_4110, plain, (![A_337, B_338]: (r2_hidden(k1_funct_1('#skF_6', u1_struct_0('#skF_5')), k3_tarski(A_337)) | v2_struct_0('#skF_5') | ~r1_tarski(A_337, k4_orders_2('#skF_5', '#skF_6')) | r1_tarski(A_337, B_338))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_4105])).
% 6.40/2.25  tff(c_4113, plain, (![A_395, B_396]: (r2_hidden(k1_funct_1('#skF_6', u1_struct_0('#skF_5')), k3_tarski(A_395)) | ~r1_tarski(A_395, k4_orders_2('#skF_5', '#skF_6')) | r1_tarski(A_395, B_396))), inference(negUnitSimplification, [status(thm)], [c_46, c_4110])).
% 6.40/2.25  tff(c_196, plain, (![D_85, A_86, B_87]: (r2_hidden(D_85, k4_orders_2(A_86, B_87)) | ~m2_orders_2(D_85, A_86, B_87) | ~m1_orders_1(B_87, k1_orders_1(u1_struct_0(A_86))) | ~l1_orders_2(A_86) | ~v5_orders_2(A_86) | ~v4_orders_2(A_86) | ~v3_orders_2(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.40/2.25  tff(c_198, plain, (![D_85]: (r2_hidden(D_85, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_85, '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_196])).
% 6.40/2.25  tff(c_201, plain, (![D_85]: (r2_hidden(D_85, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_85, '#skF_5', '#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_198])).
% 6.40/2.25  tff(c_203, plain, (![D_88]: (r2_hidden(D_88, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_88, '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_46, c_201])).
% 6.40/2.25  tff(c_221, plain, (![D_88, B_2]: (r2_hidden(D_88, B_2) | ~r1_tarski(k4_orders_2('#skF_5', '#skF_6'), B_2) | ~m2_orders_2(D_88, '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_203, c_2])).
% 6.40/2.25  tff(c_4194, plain, (![D_88, B_396]: (r2_hidden(D_88, B_396) | ~m2_orders_2(D_88, '#skF_5', '#skF_6') | r2_hidden(k1_funct_1('#skF_6', u1_struct_0('#skF_5')), k3_tarski(k4_orders_2('#skF_5', '#skF_6'))) | ~r1_tarski(k4_orders_2('#skF_5', '#skF_6'), k4_orders_2('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_4113, c_221])).
% 6.40/2.25  tff(c_4233, plain, (![D_88, B_396]: (r2_hidden(D_88, B_396) | ~m2_orders_2(D_88, '#skF_5', '#skF_6') | r2_hidden(k1_funct_1('#skF_6', u1_struct_0('#skF_5')), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_34, c_4194])).
% 6.40/2.25  tff(c_4333, plain, (![D_398, B_399]: (r2_hidden(D_398, B_399) | ~m2_orders_2(D_398, '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_4233])).
% 6.40/2.25  tff(c_4413, plain, (![B_403]: (r2_hidden('#skF_4'('#skF_5', '#skF_6'), B_403))), inference(resolution, [status(thm)], [c_120, c_4333])).
% 6.40/2.25  tff(c_4433, plain, $false, inference(resolution, [status(thm)], [c_4413, c_76])).
% 6.40/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.40/2.25  
% 6.40/2.25  Inference rules
% 6.40/2.25  ----------------------
% 6.40/2.25  #Ref     : 0
% 6.40/2.25  #Sup     : 1023
% 6.40/2.25  #Fact    : 0
% 6.40/2.25  #Define  : 0
% 6.40/2.25  #Split   : 5
% 6.40/2.25  #Chain   : 0
% 6.40/2.25  #Close   : 0
% 6.40/2.25  
% 6.40/2.25  Ordering : KBO
% 6.40/2.25  
% 6.40/2.25  Simplification rules
% 6.40/2.25  ----------------------
% 6.40/2.25  #Subsume      : 363
% 6.40/2.25  #Demod        : 506
% 6.40/2.25  #Tautology    : 240
% 6.40/2.25  #SimpNegUnit  : 73
% 6.40/2.25  #BackRed      : 60
% 6.40/2.25  
% 6.40/2.25  #Partial instantiations: 0
% 6.40/2.25  #Strategies tried      : 1
% 6.40/2.25  
% 6.40/2.25  Timing (in seconds)
% 6.40/2.25  ----------------------
% 6.40/2.26  Preprocessing        : 0.33
% 6.40/2.26  Parsing              : 0.18
% 6.40/2.26  CNF conversion       : 0.03
% 6.40/2.26  Main loop            : 1.12
% 6.40/2.26  Inferencing          : 0.37
% 6.40/2.26  Reduction            : 0.35
% 6.40/2.26  Demodulation         : 0.24
% 6.40/2.26  BG Simplification    : 0.04
% 6.40/2.26  Subsumption          : 0.29
% 6.40/2.26  Abstraction          : 0.05
% 6.40/2.26  MUC search           : 0.00
% 6.40/2.26  Cooper               : 0.00
% 6.40/2.26  Total                : 1.49
% 6.40/2.26  Index Insertion      : 0.00
% 6.40/2.26  Index Deletion       : 0.00
% 6.40/2.26  Index Matching       : 0.00
% 6.40/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
