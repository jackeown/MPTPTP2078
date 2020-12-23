%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:45 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 682 expanded)
%              Number of leaves         :   20 ( 230 expanded)
%              Depth                    :   13
%              Number of atoms          :  362 (2840 expanded)
%              Number of equality atoms :  120 ( 843 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => ( v2_funct_1(C)
        <=> ! [D,E] :
              ( ( r2_hidden(D,A)
                & r2_hidden(E,A)
                & k1_funct_1(C,D) = k1_funct_1(C,E) )
             => D = E ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_2)).

tff(c_28,plain,
    ( '#skF_5' != '#skF_6'
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_47,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_26,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_73,plain,(
    ! [B_30,A_31,C_32] :
      ( k1_xboole_0 = B_30
      | '#skF_1'(A_31,B_30,C_32) != '#skF_2'(A_31,B_30,C_32)
      | v2_funct_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_31,B_30)))
      | ~ v1_funct_2(C_32,A_31,B_30)
      | ~ v1_funct_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_76,plain,
    ( k1_xboole_0 = '#skF_3'
    | '#skF_1'('#skF_3','#skF_3','#skF_4') != '#skF_2'('#skF_3','#skF_3','#skF_4')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_73])).

tff(c_79,plain,
    ( k1_xboole_0 = '#skF_3'
    | '#skF_1'('#skF_3','#skF_3','#skF_4') != '#skF_2'('#skF_3','#skF_3','#skF_4')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_76])).

tff(c_80,plain,
    ( k1_xboole_0 = '#skF_3'
    | '#skF_1'('#skF_3','#skF_3','#skF_4') != '#skF_2'('#skF_3','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_79])).

tff(c_81,plain,(
    '#skF_1'('#skF_3','#skF_3','#skF_4') != '#skF_2'('#skF_3','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_65,plain,(
    ! [B_27,A_28,C_29] :
      ( k1_xboole_0 = B_27
      | r2_hidden('#skF_2'(A_28,B_27,C_29),A_28)
      | v2_funct_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_28,B_27)))
      | ~ v1_funct_2(C_29,A_28,B_27)
      | ~ v1_funct_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_67,plain,
    ( k1_xboole_0 = '#skF_3'
    | r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_65])).

tff(c_70,plain,
    ( k1_xboole_0 = '#skF_3'
    | r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_67])).

tff(c_71,plain,
    ( k1_xboole_0 = '#skF_3'
    | r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_70])).

tff(c_72,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_57,plain,(
    ! [B_24,A_25,C_26] :
      ( k1_xboole_0 = B_24
      | r2_hidden('#skF_1'(A_25,B_24,C_26),A_25)
      | v2_funct_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_25,B_24)))
      | ~ v1_funct_2(C_26,A_25,B_24)
      | ~ v1_funct_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_59,plain,
    ( k1_xboole_0 = '#skF_3'
    | r2_hidden('#skF_1'('#skF_3','#skF_3','#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_57])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_3'
    | r2_hidden('#skF_1'('#skF_3','#skF_3','#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_59])).

tff(c_63,plain,
    ( k1_xboole_0 = '#skF_3'
    | r2_hidden('#skF_1'('#skF_3','#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_62])).

tff(c_64,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_83,plain,(
    ! [B_35,C_36,A_37] :
      ( k1_xboole_0 = B_35
      | k1_funct_1(C_36,'#skF_1'(A_37,B_35,C_36)) = k1_funct_1(C_36,'#skF_2'(A_37,B_35,C_36))
      | v2_funct_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_35)))
      | ~ v1_funct_2(C_36,A_37,B_35)
      | ~ v1_funct_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_85,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_3','#skF_4'))
    | v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_83])).

tff(c_88,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_3','#skF_4'))
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_85])).

tff(c_89,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_88])).

tff(c_90,plain,(
    k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_46,plain,(
    ! [D_15,C_14] :
      ( v2_funct_1('#skF_4')
      | D_15 = C_14
      | k1_funct_1('#skF_4',D_15) != k1_funct_1('#skF_4',C_14)
      | ~ r2_hidden(D_15,'#skF_3')
      | ~ r2_hidden(C_14,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_48,plain,(
    ! [D_15,C_14] :
      ( D_15 = C_14
      | k1_funct_1('#skF_4',D_15) != k1_funct_1('#skF_4',C_14)
      | ~ r2_hidden(D_15,'#skF_3')
      | ~ r2_hidden(C_14,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_46])).

tff(c_93,plain,(
    ! [C_14] :
      ( C_14 = '#skF_1'('#skF_3','#skF_3','#skF_4')
      | k1_funct_1('#skF_4',C_14) != k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_3','#skF_4'))
      | ~ r2_hidden('#skF_1'('#skF_3','#skF_3','#skF_4'),'#skF_3')
      | ~ r2_hidden(C_14,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_48])).

tff(c_99,plain,(
    ! [C_14] :
      ( C_14 = '#skF_1'('#skF_3','#skF_3','#skF_4')
      | k1_funct_1('#skF_4',C_14) != k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_3','#skF_4'))
      | ~ r2_hidden(C_14,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_93])).

tff(c_105,plain,
    ( '#skF_1'('#skF_3','#skF_3','#skF_4') = '#skF_2'('#skF_3','#skF_3','#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_4'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_99])).

tff(c_107,plain,(
    '#skF_1'('#skF_3','#skF_3','#skF_4') = '#skF_2'('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_105])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_107])).

tff(c_111,plain,(
    k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4')) != k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_110,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_6,plain,(
    ! [C_3,B_2] :
      ( k1_funct_1(C_3,'#skF_1'(k1_xboole_0,B_2,C_3)) = k1_funct_1(C_3,'#skF_2'(k1_xboole_0,B_2,C_3))
      | v2_funct_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_2(C_3,k1_xboole_0,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_184,plain,(
    ! [C_62,B_63] :
      ( k1_funct_1(C_62,'#skF_1'('#skF_3',B_63,C_62)) = k1_funct_1(C_62,'#skF_2'('#skF_3',B_63,C_62))
      | v2_funct_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_63)))
      | ~ v1_funct_2(C_62,'#skF_3',B_63)
      | ~ v1_funct_1(C_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_110,c_110,c_110,c_6])).

tff(c_186,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_3','#skF_4'))
    | v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_184])).

tff(c_189,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_3','#skF_4'))
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_186])).

tff(c_191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_111,c_189])).

tff(c_193,plain,(
    '#skF_1'('#skF_3','#skF_3','#skF_4') = '#skF_2'('#skF_3','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_192,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_2,plain,(
    ! [B_2,C_3] :
      ( '#skF_1'(k1_xboole_0,B_2,C_3) != '#skF_2'(k1_xboole_0,B_2,C_3)
      | v2_funct_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_2(C_3,k1_xboole_0,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_234,plain,(
    ! [B_70,C_71] :
      ( '#skF_1'('#skF_3',B_70,C_71) != '#skF_2'('#skF_3',B_70,C_71)
      | v2_funct_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_70)))
      | ~ v1_funct_2(C_71,'#skF_3',B_70)
      | ~ v1_funct_1(C_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_192,c_192,c_192,c_2])).

tff(c_237,plain,
    ( '#skF_1'('#skF_3','#skF_3','#skF_4') != '#skF_2'('#skF_3','#skF_3','#skF_4')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_234])).

tff(c_240,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_193,c_237])).

tff(c_242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_240])).

tff(c_244,plain,(
    ~ r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_243,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_10,plain,(
    ! [B_2,C_3] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_2,C_3),k1_xboole_0)
      | v2_funct_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_2(C_3,k1_xboole_0,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_264,plain,(
    ! [B_75,C_76] :
      ( r2_hidden('#skF_2'('#skF_3',B_75,C_76),'#skF_3')
      | v2_funct_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_75)))
      | ~ v1_funct_2(C_76,'#skF_3',B_75)
      | ~ v1_funct_1(C_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_243,c_243,c_243,c_10])).

tff(c_267,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_264])).

tff(c_270,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_267])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_244,c_270])).

tff(c_274,plain,(
    ~ r2_hidden('#skF_1'('#skF_3','#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_273,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_14,plain,(
    ! [B_2,C_3] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_2,C_3),k1_xboole_0)
      | v2_funct_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_2(C_3,k1_xboole_0,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_300,plain,(
    ! [B_82,C_83] :
      ( r2_hidden('#skF_1'('#skF_3',B_82,C_83),'#skF_3')
      | v2_funct_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_82)))
      | ~ v1_funct_2(C_83,'#skF_3',B_82)
      | ~ v1_funct_1(C_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_273,c_273,c_273,c_14])).

tff(c_303,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_3','#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_300])).

tff(c_306,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_3','#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_303])).

tff(c_308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_274,c_306])).

tff(c_309,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_310,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_32,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_312,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_32])).

tff(c_34,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_314,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_34])).

tff(c_30,plain,
    ( k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_316,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_30])).

tff(c_499,plain,(
    ! [A_134,C_133,B_132,D_131,E_135] :
      ( k1_xboole_0 = B_132
      | E_135 = D_131
      | k1_funct_1(C_133,E_135) != k1_funct_1(C_133,D_131)
      | ~ r2_hidden(E_135,A_134)
      | ~ r2_hidden(D_131,A_134)
      | ~ v2_funct_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_134,B_132)))
      | ~ v1_funct_2(C_133,A_134,B_132)
      | ~ v1_funct_1(C_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_501,plain,(
    ! [B_132,D_131,A_134] :
      ( k1_xboole_0 = B_132
      | D_131 = '#skF_5'
      | k1_funct_1('#skF_4',D_131) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',A_134)
      | ~ r2_hidden(D_131,A_134)
      | ~ v2_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_134,B_132)))
      | ~ v1_funct_2('#skF_4',A_134,B_132)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_499])).

tff(c_518,plain,(
    ! [B_137,D_138,A_139] :
      ( k1_xboole_0 = B_137
      | D_138 = '#skF_5'
      | k1_funct_1('#skF_4',D_138) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',A_139)
      | ~ r2_hidden(D_138,A_139)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_139,B_137)))
      | ~ v1_funct_2('#skF_4',A_139,B_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_310,c_501])).

tff(c_524,plain,(
    ! [B_137] :
      ( k1_xboole_0 = B_137
      | '#skF_5' = '#skF_6'
      | ~ r2_hidden('#skF_5','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_137)))
      | ~ v1_funct_2('#skF_4','#skF_3',B_137) ) ),
    inference(resolution,[status(thm)],[c_312,c_518])).

tff(c_535,plain,(
    ! [B_137] :
      ( k1_xboole_0 = B_137
      | '#skF_5' = '#skF_6'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_137)))
      | ~ v1_funct_2('#skF_4','#skF_3',B_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_524])).

tff(c_537,plain,(
    ! [B_140] :
      ( k1_xboole_0 = B_140
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_140)))
      | ~ v1_funct_2('#skF_4','#skF_3',B_140) ) ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_535])).

tff(c_540,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_537])).

tff(c_543,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_540])).

tff(c_433,plain,(
    ! [A_124,B_122,D_121,E_125,C_123] :
      ( k1_xboole_0 = B_122
      | E_125 = D_121
      | k1_funct_1(C_123,E_125) != k1_funct_1(C_123,D_121)
      | ~ r2_hidden(E_125,A_124)
      | ~ r2_hidden(D_121,A_124)
      | ~ v2_funct_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_122)))
      | ~ v1_funct_2(C_123,A_124,B_122)
      | ~ v1_funct_1(C_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_435,plain,(
    ! [B_122,D_121,A_124] :
      ( k1_xboole_0 = B_122
      | D_121 = '#skF_5'
      | k1_funct_1('#skF_4',D_121) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',A_124)
      | ~ r2_hidden(D_121,A_124)
      | ~ v2_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_124,B_122)))
      | ~ v1_funct_2('#skF_4',A_124,B_122)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_433])).

tff(c_442,plain,(
    ! [B_126,D_127,A_128] :
      ( k1_xboole_0 = B_126
      | D_127 = '#skF_5'
      | k1_funct_1('#skF_4',D_127) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',A_128)
      | ~ r2_hidden(D_127,A_128)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_128,B_126)))
      | ~ v1_funct_2('#skF_4',A_128,B_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_310,c_435])).

tff(c_448,plain,(
    ! [B_126] :
      ( k1_xboole_0 = B_126
      | '#skF_5' = '#skF_6'
      | ~ r2_hidden('#skF_5','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_126)))
      | ~ v1_funct_2('#skF_4','#skF_3',B_126) ) ),
    inference(resolution,[status(thm)],[c_312,c_442])).

tff(c_458,plain,(
    ! [B_126] :
      ( k1_xboole_0 = B_126
      | '#skF_5' = '#skF_6'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_126)))
      | ~ v1_funct_2('#skF_4','#skF_3',B_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_448])).

tff(c_460,plain,(
    ! [B_129] :
      ( k1_xboole_0 = B_129
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_129)))
      | ~ v1_funct_2('#skF_4','#skF_3',B_129) ) ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_458])).

tff(c_463,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_460])).

tff(c_466,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_463])).

tff(c_372,plain,(
    ! [C_110,D_108,A_111,B_109,E_112] :
      ( k1_xboole_0 = B_109
      | E_112 = D_108
      | k1_funct_1(C_110,E_112) != k1_funct_1(C_110,D_108)
      | ~ r2_hidden(E_112,A_111)
      | ~ r2_hidden(D_108,A_111)
      | ~ v2_funct_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_109)))
      | ~ v1_funct_2(C_110,A_111,B_109)
      | ~ v1_funct_1(C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_374,plain,(
    ! [B_109,D_108,A_111] :
      ( k1_xboole_0 = B_109
      | D_108 = '#skF_5'
      | k1_funct_1('#skF_4',D_108) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',A_111)
      | ~ r2_hidden(D_108,A_111)
      | ~ v2_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_111,B_109)))
      | ~ v1_funct_2('#skF_4',A_111,B_109)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_372])).

tff(c_381,plain,(
    ! [B_113,D_114,A_115] :
      ( k1_xboole_0 = B_113
      | D_114 = '#skF_5'
      | k1_funct_1('#skF_4',D_114) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',A_115)
      | ~ r2_hidden(D_114,A_115)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_115,B_113)))
      | ~ v1_funct_2('#skF_4',A_115,B_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_310,c_374])).

tff(c_385,plain,(
    ! [B_113] :
      ( k1_xboole_0 = B_113
      | '#skF_5' = '#skF_6'
      | ~ r2_hidden('#skF_5','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_113)))
      | ~ v1_funct_2('#skF_4','#skF_3',B_113) ) ),
    inference(resolution,[status(thm)],[c_312,c_381])).

tff(c_392,plain,(
    ! [B_113] :
      ( k1_xboole_0 = B_113
      | '#skF_5' = '#skF_6'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_113)))
      | ~ v1_funct_2('#skF_4','#skF_3',B_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_385])).

tff(c_394,plain,(
    ! [B_116] :
      ( k1_xboole_0 = B_116
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_116)))
      | ~ v1_funct_2('#skF_4','#skF_3',B_116) ) ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_392])).

tff(c_397,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_394])).

tff(c_400,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_397])).

tff(c_352,plain,(
    ! [E_101,D_102,C_103,B_104] :
      ( E_101 = D_102
      | k1_funct_1(C_103,E_101) != k1_funct_1(C_103,D_102)
      | ~ r2_hidden(E_101,k1_xboole_0)
      | ~ r2_hidden(D_102,k1_xboole_0)
      | ~ v2_funct_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_104)))
      | ~ v1_funct_2(C_103,k1_xboole_0,B_104)
      | ~ v1_funct_1(C_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_354,plain,(
    ! [D_102,B_104] :
      ( D_102 = '#skF_5'
      | k1_funct_1('#skF_4',D_102) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',k1_xboole_0)
      | ~ r2_hidden(D_102,k1_xboole_0)
      | ~ v2_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_104)))
      | ~ v1_funct_2('#skF_4',k1_xboole_0,B_104)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_352])).

tff(c_358,plain,(
    ! [D_102,B_104] :
      ( D_102 = '#skF_5'
      | k1_funct_1('#skF_4',D_102) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',k1_xboole_0)
      | ~ r2_hidden(D_102,k1_xboole_0)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_104)))
      | ~ v1_funct_2('#skF_4',k1_xboole_0,B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_310,c_354])).

tff(c_361,plain,(
    ~ r2_hidden('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_358])).

tff(c_405,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_361])).

tff(c_416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_405])).

tff(c_417,plain,(
    ! [B_104,D_102] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_104)))
      | ~ v1_funct_2('#skF_4',k1_xboole_0,B_104)
      | D_102 = '#skF_5'
      | k1_funct_1('#skF_4',D_102) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(D_102,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_425,plain,(
    ! [B_104] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_104)))
      | ~ v1_funct_2('#skF_4',k1_xboole_0,B_104) ) ),
    inference(splitLeft,[status(thm)],[c_417])).

tff(c_486,plain,(
    ! [B_130] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_130)))
      | ~ v1_funct_2('#skF_4','#skF_3',B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_466,c_425])).

tff(c_489,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_486])).

tff(c_493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_489])).

tff(c_494,plain,(
    ! [D_102] :
      ( D_102 = '#skF_5'
      | k1_funct_1('#skF_4',D_102) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(D_102,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_417])).

tff(c_563,plain,(
    ! [D_141] :
      ( D_141 = '#skF_5'
      | k1_funct_1('#skF_4',D_141) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(D_141,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_494])).

tff(c_569,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_312,c_563])).

tff(c_577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_569])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:32:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.92  
% 3.39/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.93  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.39/1.93  
% 3.39/1.93  %Foreground sorts:
% 3.39/1.93  
% 3.39/1.93  
% 3.39/1.93  %Background operators:
% 3.39/1.93  
% 3.39/1.93  
% 3.39/1.93  %Foreground operators:
% 3.39/1.93  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.39/1.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.39/1.93  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.39/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.39/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.39/1.93  tff('#skF_5', type, '#skF_5': $i).
% 3.39/1.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.39/1.93  tff('#skF_6', type, '#skF_6': $i).
% 3.39/1.93  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.93  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.39/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.39/1.93  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.39/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.39/1.93  tff('#skF_4', type, '#skF_4': $i).
% 3.39/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.39/1.93  
% 3.62/1.96  tff(f_64, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_funct_2)).
% 3.62/1.96  tff(f_46, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (v2_funct_1(C) <=> (![D, E]: (((r2_hidden(D, A) & r2_hidden(E, A)) & (k1_funct_1(C, D) = k1_funct_1(C, E))) => (D = E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_funct_2)).
% 3.62/1.96  tff(c_28, plain, ('#skF_5'!='#skF_6' | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.62/1.96  tff(c_47, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_28])).
% 3.62/1.96  tff(c_26, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.62/1.96  tff(c_24, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.62/1.96  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.62/1.96  tff(c_73, plain, (![B_30, A_31, C_32]: (k1_xboole_0=B_30 | '#skF_1'(A_31, B_30, C_32)!='#skF_2'(A_31, B_30, C_32) | v2_funct_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_31, B_30))) | ~v1_funct_2(C_32, A_31, B_30) | ~v1_funct_1(C_32))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.62/1.96  tff(c_76, plain, (k1_xboole_0='#skF_3' | '#skF_1'('#skF_3', '#skF_3', '#skF_4')!='#skF_2'('#skF_3', '#skF_3', '#skF_4') | v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_73])).
% 3.62/1.96  tff(c_79, plain, (k1_xboole_0='#skF_3' | '#skF_1'('#skF_3', '#skF_3', '#skF_4')!='#skF_2'('#skF_3', '#skF_3', '#skF_4') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_76])).
% 3.62/1.96  tff(c_80, plain, (k1_xboole_0='#skF_3' | '#skF_1'('#skF_3', '#skF_3', '#skF_4')!='#skF_2'('#skF_3', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_47, c_79])).
% 3.62/1.96  tff(c_81, plain, ('#skF_1'('#skF_3', '#skF_3', '#skF_4')!='#skF_2'('#skF_3', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_80])).
% 3.62/1.96  tff(c_65, plain, (![B_27, A_28, C_29]: (k1_xboole_0=B_27 | r2_hidden('#skF_2'(A_28, B_27, C_29), A_28) | v2_funct_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_28, B_27))) | ~v1_funct_2(C_29, A_28, B_27) | ~v1_funct_1(C_29))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.62/1.96  tff(c_67, plain, (k1_xboole_0='#skF_3' | r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_65])).
% 3.62/1.96  tff(c_70, plain, (k1_xboole_0='#skF_3' | r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_67])).
% 3.62/1.96  tff(c_71, plain, (k1_xboole_0='#skF_3' | r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_47, c_70])).
% 3.62/1.96  tff(c_72, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_71])).
% 3.62/1.96  tff(c_57, plain, (![B_24, A_25, C_26]: (k1_xboole_0=B_24 | r2_hidden('#skF_1'(A_25, B_24, C_26), A_25) | v2_funct_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_25, B_24))) | ~v1_funct_2(C_26, A_25, B_24) | ~v1_funct_1(C_26))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.62/1.96  tff(c_59, plain, (k1_xboole_0='#skF_3' | r2_hidden('#skF_1'('#skF_3', '#skF_3', '#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_57])).
% 3.62/1.96  tff(c_62, plain, (k1_xboole_0='#skF_3' | r2_hidden('#skF_1'('#skF_3', '#skF_3', '#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_59])).
% 3.62/1.96  tff(c_63, plain, (k1_xboole_0='#skF_3' | r2_hidden('#skF_1'('#skF_3', '#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_47, c_62])).
% 3.62/1.96  tff(c_64, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_63])).
% 3.62/1.96  tff(c_83, plain, (![B_35, C_36, A_37]: (k1_xboole_0=B_35 | k1_funct_1(C_36, '#skF_1'(A_37, B_35, C_36))=k1_funct_1(C_36, '#skF_2'(A_37, B_35, C_36)) | v2_funct_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_35))) | ~v1_funct_2(C_36, A_37, B_35) | ~v1_funct_1(C_36))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.62/1.96  tff(c_85, plain, (k1_xboole_0='#skF_3' | k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_3', '#skF_4')) | v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_83])).
% 3.62/1.96  tff(c_88, plain, (k1_xboole_0='#skF_3' | k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_3', '#skF_4')) | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_85])).
% 3.62/1.96  tff(c_89, plain, (k1_xboole_0='#skF_3' | k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_47, c_88])).
% 3.62/1.96  tff(c_90, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_89])).
% 3.62/1.96  tff(c_46, plain, (![D_15, C_14]: (v2_funct_1('#skF_4') | D_15=C_14 | k1_funct_1('#skF_4', D_15)!=k1_funct_1('#skF_4', C_14) | ~r2_hidden(D_15, '#skF_3') | ~r2_hidden(C_14, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.62/1.96  tff(c_48, plain, (![D_15, C_14]: (D_15=C_14 | k1_funct_1('#skF_4', D_15)!=k1_funct_1('#skF_4', C_14) | ~r2_hidden(D_15, '#skF_3') | ~r2_hidden(C_14, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_47, c_46])).
% 3.62/1.96  tff(c_93, plain, (![C_14]: (C_14='#skF_1'('#skF_3', '#skF_3', '#skF_4') | k1_funct_1('#skF_4', C_14)!=k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_3', '#skF_4')) | ~r2_hidden('#skF_1'('#skF_3', '#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden(C_14, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_48])).
% 3.62/1.96  tff(c_99, plain, (![C_14]: (C_14='#skF_1'('#skF_3', '#skF_3', '#skF_4') | k1_funct_1('#skF_4', C_14)!=k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_3', '#skF_4')) | ~r2_hidden(C_14, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_93])).
% 3.62/1.96  tff(c_105, plain, ('#skF_1'('#skF_3', '#skF_3', '#skF_4')='#skF_2'('#skF_3', '#skF_3', '#skF_4') | ~r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_4'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_99])).
% 3.62/1.96  tff(c_107, plain, ('#skF_1'('#skF_3', '#skF_3', '#skF_4')='#skF_2'('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_105])).
% 3.62/1.96  tff(c_109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_107])).
% 3.62/1.96  tff(c_111, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4'))!=k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_89])).
% 3.62/1.96  tff(c_110, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_89])).
% 3.62/1.96  tff(c_6, plain, (![C_3, B_2]: (k1_funct_1(C_3, '#skF_1'(k1_xboole_0, B_2, C_3))=k1_funct_1(C_3, '#skF_2'(k1_xboole_0, B_2, C_3)) | v2_funct_1(C_3) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))) | ~v1_funct_2(C_3, k1_xboole_0, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.62/1.96  tff(c_184, plain, (![C_62, B_63]: (k1_funct_1(C_62, '#skF_1'('#skF_3', B_63, C_62))=k1_funct_1(C_62, '#skF_2'('#skF_3', B_63, C_62)) | v2_funct_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_63))) | ~v1_funct_2(C_62, '#skF_3', B_63) | ~v1_funct_1(C_62))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_110, c_110, c_110, c_6])).
% 3.62/1.96  tff(c_186, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_3', '#skF_4')) | v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_184])).
% 3.62/1.96  tff(c_189, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_3', '#skF_4')) | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_186])).
% 3.62/1.96  tff(c_191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_111, c_189])).
% 3.62/1.96  tff(c_193, plain, ('#skF_1'('#skF_3', '#skF_3', '#skF_4')='#skF_2'('#skF_3', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_80])).
% 3.62/1.96  tff(c_192, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_80])).
% 3.62/1.96  tff(c_2, plain, (![B_2, C_3]: ('#skF_1'(k1_xboole_0, B_2, C_3)!='#skF_2'(k1_xboole_0, B_2, C_3) | v2_funct_1(C_3) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))) | ~v1_funct_2(C_3, k1_xboole_0, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.62/1.96  tff(c_234, plain, (![B_70, C_71]: ('#skF_1'('#skF_3', B_70, C_71)!='#skF_2'('#skF_3', B_70, C_71) | v2_funct_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_70))) | ~v1_funct_2(C_71, '#skF_3', B_70) | ~v1_funct_1(C_71))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_192, c_192, c_192, c_2])).
% 3.62/1.96  tff(c_237, plain, ('#skF_1'('#skF_3', '#skF_3', '#skF_4')!='#skF_2'('#skF_3', '#skF_3', '#skF_4') | v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_234])).
% 3.62/1.96  tff(c_240, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_193, c_237])).
% 3.62/1.96  tff(c_242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_240])).
% 3.62/1.96  tff(c_244, plain, (~r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_71])).
% 3.62/1.96  tff(c_243, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_71])).
% 3.62/1.96  tff(c_10, plain, (![B_2, C_3]: (r2_hidden('#skF_2'(k1_xboole_0, B_2, C_3), k1_xboole_0) | v2_funct_1(C_3) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))) | ~v1_funct_2(C_3, k1_xboole_0, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.62/1.96  tff(c_264, plain, (![B_75, C_76]: (r2_hidden('#skF_2'('#skF_3', B_75, C_76), '#skF_3') | v2_funct_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_75))) | ~v1_funct_2(C_76, '#skF_3', B_75) | ~v1_funct_1(C_76))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_243, c_243, c_243, c_10])).
% 3.62/1.96  tff(c_267, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_264])).
% 3.62/1.96  tff(c_270, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_267])).
% 3.62/1.96  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_244, c_270])).
% 3.62/1.96  tff(c_274, plain, (~r2_hidden('#skF_1'('#skF_3', '#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_63])).
% 3.62/1.96  tff(c_273, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_63])).
% 3.62/1.96  tff(c_14, plain, (![B_2, C_3]: (r2_hidden('#skF_1'(k1_xboole_0, B_2, C_3), k1_xboole_0) | v2_funct_1(C_3) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))) | ~v1_funct_2(C_3, k1_xboole_0, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.62/1.96  tff(c_300, plain, (![B_82, C_83]: (r2_hidden('#skF_1'('#skF_3', B_82, C_83), '#skF_3') | v2_funct_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_82))) | ~v1_funct_2(C_83, '#skF_3', B_82) | ~v1_funct_1(C_83))), inference(demodulation, [status(thm), theory('equality')], [c_273, c_273, c_273, c_273, c_14])).
% 3.62/1.96  tff(c_303, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_3', '#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_300])).
% 3.62/1.96  tff(c_306, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_3', '#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_303])).
% 3.62/1.96  tff(c_308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_274, c_306])).
% 3.62/1.96  tff(c_309, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_28])).
% 3.62/1.96  tff(c_310, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_28])).
% 3.62/1.96  tff(c_32, plain, (r2_hidden('#skF_6', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.62/1.96  tff(c_312, plain, (r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_310, c_32])).
% 3.62/1.96  tff(c_34, plain, (r2_hidden('#skF_5', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.62/1.96  tff(c_314, plain, (r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_310, c_34])).
% 3.62/1.96  tff(c_30, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.62/1.96  tff(c_316, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_310, c_30])).
% 3.62/1.96  tff(c_499, plain, (![A_134, C_133, B_132, D_131, E_135]: (k1_xboole_0=B_132 | E_135=D_131 | k1_funct_1(C_133, E_135)!=k1_funct_1(C_133, D_131) | ~r2_hidden(E_135, A_134) | ~r2_hidden(D_131, A_134) | ~v2_funct_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_134, B_132))) | ~v1_funct_2(C_133, A_134, B_132) | ~v1_funct_1(C_133))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.62/1.96  tff(c_501, plain, (![B_132, D_131, A_134]: (k1_xboole_0=B_132 | D_131='#skF_5' | k1_funct_1('#skF_4', D_131)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', A_134) | ~r2_hidden(D_131, A_134) | ~v2_funct_1('#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_134, B_132))) | ~v1_funct_2('#skF_4', A_134, B_132) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_316, c_499])).
% 3.62/1.96  tff(c_518, plain, (![B_137, D_138, A_139]: (k1_xboole_0=B_137 | D_138='#skF_5' | k1_funct_1('#skF_4', D_138)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', A_139) | ~r2_hidden(D_138, A_139) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_139, B_137))) | ~v1_funct_2('#skF_4', A_139, B_137))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_310, c_501])).
% 3.62/1.96  tff(c_524, plain, (![B_137]: (k1_xboole_0=B_137 | '#skF_5'='#skF_6' | ~r2_hidden('#skF_5', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_137))) | ~v1_funct_2('#skF_4', '#skF_3', B_137))), inference(resolution, [status(thm)], [c_312, c_518])).
% 3.62/1.96  tff(c_535, plain, (![B_137]: (k1_xboole_0=B_137 | '#skF_5'='#skF_6' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_137))) | ~v1_funct_2('#skF_4', '#skF_3', B_137))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_524])).
% 3.62/1.96  tff(c_537, plain, (![B_140]: (k1_xboole_0=B_140 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_140))) | ~v1_funct_2('#skF_4', '#skF_3', B_140))), inference(negUnitSimplification, [status(thm)], [c_309, c_535])).
% 3.62/1.96  tff(c_540, plain, (k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_537])).
% 3.62/1.96  tff(c_543, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_540])).
% 3.62/1.96  tff(c_433, plain, (![A_124, B_122, D_121, E_125, C_123]: (k1_xboole_0=B_122 | E_125=D_121 | k1_funct_1(C_123, E_125)!=k1_funct_1(C_123, D_121) | ~r2_hidden(E_125, A_124) | ~r2_hidden(D_121, A_124) | ~v2_funct_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_122))) | ~v1_funct_2(C_123, A_124, B_122) | ~v1_funct_1(C_123))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.62/1.96  tff(c_435, plain, (![B_122, D_121, A_124]: (k1_xboole_0=B_122 | D_121='#skF_5' | k1_funct_1('#skF_4', D_121)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', A_124) | ~r2_hidden(D_121, A_124) | ~v2_funct_1('#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_124, B_122))) | ~v1_funct_2('#skF_4', A_124, B_122) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_316, c_433])).
% 3.62/1.96  tff(c_442, plain, (![B_126, D_127, A_128]: (k1_xboole_0=B_126 | D_127='#skF_5' | k1_funct_1('#skF_4', D_127)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', A_128) | ~r2_hidden(D_127, A_128) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_128, B_126))) | ~v1_funct_2('#skF_4', A_128, B_126))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_310, c_435])).
% 3.62/1.96  tff(c_448, plain, (![B_126]: (k1_xboole_0=B_126 | '#skF_5'='#skF_6' | ~r2_hidden('#skF_5', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_126))) | ~v1_funct_2('#skF_4', '#skF_3', B_126))), inference(resolution, [status(thm)], [c_312, c_442])).
% 3.62/1.96  tff(c_458, plain, (![B_126]: (k1_xboole_0=B_126 | '#skF_5'='#skF_6' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_126))) | ~v1_funct_2('#skF_4', '#skF_3', B_126))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_448])).
% 3.62/1.96  tff(c_460, plain, (![B_129]: (k1_xboole_0=B_129 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_129))) | ~v1_funct_2('#skF_4', '#skF_3', B_129))), inference(negUnitSimplification, [status(thm)], [c_309, c_458])).
% 3.62/1.96  tff(c_463, plain, (k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_460])).
% 3.62/1.96  tff(c_466, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_463])).
% 3.62/1.96  tff(c_372, plain, (![C_110, D_108, A_111, B_109, E_112]: (k1_xboole_0=B_109 | E_112=D_108 | k1_funct_1(C_110, E_112)!=k1_funct_1(C_110, D_108) | ~r2_hidden(E_112, A_111) | ~r2_hidden(D_108, A_111) | ~v2_funct_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_109))) | ~v1_funct_2(C_110, A_111, B_109) | ~v1_funct_1(C_110))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.62/1.96  tff(c_374, plain, (![B_109, D_108, A_111]: (k1_xboole_0=B_109 | D_108='#skF_5' | k1_funct_1('#skF_4', D_108)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', A_111) | ~r2_hidden(D_108, A_111) | ~v2_funct_1('#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_111, B_109))) | ~v1_funct_2('#skF_4', A_111, B_109) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_316, c_372])).
% 3.62/1.96  tff(c_381, plain, (![B_113, D_114, A_115]: (k1_xboole_0=B_113 | D_114='#skF_5' | k1_funct_1('#skF_4', D_114)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', A_115) | ~r2_hidden(D_114, A_115) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_115, B_113))) | ~v1_funct_2('#skF_4', A_115, B_113))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_310, c_374])).
% 3.62/1.96  tff(c_385, plain, (![B_113]: (k1_xboole_0=B_113 | '#skF_5'='#skF_6' | ~r2_hidden('#skF_5', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_113))) | ~v1_funct_2('#skF_4', '#skF_3', B_113))), inference(resolution, [status(thm)], [c_312, c_381])).
% 3.62/1.96  tff(c_392, plain, (![B_113]: (k1_xboole_0=B_113 | '#skF_5'='#skF_6' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_113))) | ~v1_funct_2('#skF_4', '#skF_3', B_113))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_385])).
% 3.62/1.96  tff(c_394, plain, (![B_116]: (k1_xboole_0=B_116 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_116))) | ~v1_funct_2('#skF_4', '#skF_3', B_116))), inference(negUnitSimplification, [status(thm)], [c_309, c_392])).
% 3.62/1.96  tff(c_397, plain, (k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_394])).
% 3.62/1.96  tff(c_400, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_397])).
% 3.62/1.96  tff(c_352, plain, (![E_101, D_102, C_103, B_104]: (E_101=D_102 | k1_funct_1(C_103, E_101)!=k1_funct_1(C_103, D_102) | ~r2_hidden(E_101, k1_xboole_0) | ~r2_hidden(D_102, k1_xboole_0) | ~v2_funct_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_104))) | ~v1_funct_2(C_103, k1_xboole_0, B_104) | ~v1_funct_1(C_103))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.62/1.96  tff(c_354, plain, (![D_102, B_104]: (D_102='#skF_5' | k1_funct_1('#skF_4', D_102)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', k1_xboole_0) | ~r2_hidden(D_102, k1_xboole_0) | ~v2_funct_1('#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_104))) | ~v1_funct_2('#skF_4', k1_xboole_0, B_104) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_316, c_352])).
% 3.62/1.96  tff(c_358, plain, (![D_102, B_104]: (D_102='#skF_5' | k1_funct_1('#skF_4', D_102)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', k1_xboole_0) | ~r2_hidden(D_102, k1_xboole_0) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_104))) | ~v1_funct_2('#skF_4', k1_xboole_0, B_104))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_310, c_354])).
% 3.62/1.96  tff(c_361, plain, (~r2_hidden('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_358])).
% 3.62/1.96  tff(c_405, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_400, c_361])).
% 3.62/1.96  tff(c_416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_314, c_405])).
% 3.62/1.96  tff(c_417, plain, (![B_104, D_102]: (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_104))) | ~v1_funct_2('#skF_4', k1_xboole_0, B_104) | D_102='#skF_5' | k1_funct_1('#skF_4', D_102)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(D_102, k1_xboole_0))), inference(splitRight, [status(thm)], [c_358])).
% 3.62/1.96  tff(c_425, plain, (![B_104]: (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_104))) | ~v1_funct_2('#skF_4', k1_xboole_0, B_104))), inference(splitLeft, [status(thm)], [c_417])).
% 3.62/1.96  tff(c_486, plain, (![B_130]: (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_130))) | ~v1_funct_2('#skF_4', '#skF_3', B_130))), inference(demodulation, [status(thm), theory('equality')], [c_466, c_466, c_425])).
% 3.62/1.96  tff(c_489, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_486])).
% 3.62/1.96  tff(c_493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_489])).
% 3.62/1.96  tff(c_494, plain, (![D_102]: (D_102='#skF_5' | k1_funct_1('#skF_4', D_102)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(D_102, k1_xboole_0))), inference(splitRight, [status(thm)], [c_417])).
% 3.62/1.96  tff(c_563, plain, (![D_141]: (D_141='#skF_5' | k1_funct_1('#skF_4', D_141)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(D_141, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_543, c_494])).
% 3.62/1.96  tff(c_569, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_312, c_563])).
% 3.62/1.96  tff(c_577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_309, c_569])).
% 3.62/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.96  
% 3.62/1.96  Inference rules
% 3.62/1.96  ----------------------
% 3.62/1.96  #Ref     : 8
% 3.62/1.96  #Sup     : 68
% 3.62/1.96  #Fact    : 0
% 3.62/1.96  #Define  : 0
% 3.62/1.96  #Split   : 7
% 3.62/1.96  #Chain   : 0
% 3.62/1.96  #Close   : 0
% 3.62/1.96  
% 3.62/1.96  Ordering : KBO
% 3.62/1.96  
% 3.62/1.96  Simplification rules
% 3.62/1.96  ----------------------
% 3.62/1.96  #Subsume      : 14
% 3.62/1.96  #Demod        : 277
% 3.62/1.96  #Tautology    : 53
% 3.62/1.96  #SimpNegUnit  : 26
% 3.62/1.96  #BackRed      : 65
% 3.62/1.96  
% 3.62/1.96  #Partial instantiations: 0
% 3.62/1.96  #Strategies tried      : 1
% 3.62/1.96  
% 3.62/1.96  Timing (in seconds)
% 3.62/1.96  ----------------------
% 3.62/1.97  Preprocessing        : 0.48
% 3.62/1.97  Parsing              : 0.23
% 3.62/1.97  CNF conversion       : 0.03
% 3.62/1.97  Main loop            : 0.53
% 3.62/1.97  Inferencing          : 0.18
% 3.62/1.97  Reduction            : 0.18
% 3.62/1.97  Demodulation         : 0.11
% 3.62/1.97  BG Simplification    : 0.04
% 3.62/1.97  Subsumption          : 0.09
% 3.62/1.97  Abstraction          : 0.03
% 3.62/1.97  MUC search           : 0.00
% 3.62/1.97  Cooper               : 0.00
% 3.62/1.97  Total                : 1.09
% 3.62/1.97  Index Insertion      : 0.00
% 3.62/1.97  Index Deletion       : 0.00
% 3.62/1.97  Index Matching       : 0.00
% 3.62/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
