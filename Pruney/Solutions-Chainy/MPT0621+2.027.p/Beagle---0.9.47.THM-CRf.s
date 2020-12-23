%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:02 EST 2020

% Result     : Theorem 18.93s
% Output     : CNFRefutation 18.93s
% Verified   : 
% Statistics : Number of formulae       :   92 (2187 expanded)
%              Number of leaves         :   25 ( 734 expanded)
%              Depth                    :   21
%              Number of atoms          :  183 (5818 expanded)
%              Number of equality atoms :  100 (2850 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(np__1,type,(
    np__1: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( k1_relat_1(B) = A
                    & k1_relat_1(C) = A )
                 => B = C ) ) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_68,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_36,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32,plain,(
    ! [A_28] : k1_relat_1('#skF_6'(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    ! [A_28] : v1_relat_1('#skF_6'(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_82,plain,(
    ! [A_51] :
      ( k1_relat_1(A_51) != k1_xboole_0
      | k1_xboole_0 = A_51
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_88,plain,(
    ! [A_28] :
      ( k1_relat_1('#skF_6'(A_28)) != k1_xboole_0
      | '#skF_6'(A_28) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_36,c_82])).

tff(c_93,plain,(
    '#skF_6'(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_88])).

tff(c_876,plain,(
    ! [A_866,B_867] :
      ( r2_hidden(k4_tarski('#skF_1'(A_866,B_867),'#skF_2'(A_866,B_867)),A_866)
      | r2_hidden('#skF_3'(A_866,B_867),B_867)
      | k1_relat_1(A_866) = B_867 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k1_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(C_16,D_19),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_976,plain,(
    ! [A_946,B_947] :
      ( r2_hidden('#skF_1'(A_946,B_947),k1_relat_1(A_946))
      | r2_hidden('#skF_3'(A_946,B_947),B_947)
      | k1_relat_1(A_946) = B_947 ) ),
    inference(resolution,[status(thm)],[c_876,c_4])).

tff(c_1002,plain,(
    ! [A_28,B_947] :
      ( r2_hidden('#skF_1'('#skF_6'(A_28),B_947),A_28)
      | r2_hidden('#skF_3'('#skF_6'(A_28),B_947),B_947)
      | k1_relat_1('#skF_6'(A_28)) = B_947 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_976])).

tff(c_1013,plain,(
    ! [A_28,B_947] :
      ( r2_hidden('#skF_1'('#skF_6'(A_28),B_947),A_28)
      | r2_hidden('#skF_3'('#skF_6'(A_28),B_947),B_947)
      | B_947 = A_28 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1002])).

tff(c_2249,plain,(
    ! [A_2113,B_2114] :
      ( r2_hidden('#skF_1'('#skF_6'(A_2113),B_2114),A_2113)
      | r2_hidden('#skF_3'('#skF_6'(A_2113),B_2114),B_2114)
      | B_2114 = A_2113 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1002])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_394,plain,(
    ! [C_84,A_85] :
      ( r2_hidden(k4_tarski(C_84,'#skF_4'(A_85,k1_relat_1(A_85),C_84)),A_85)
      | ~ r2_hidden(C_84,k1_relat_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_408,plain,(
    ! [C_84] :
      ( r2_hidden(k4_tarski(C_84,'#skF_4'(k1_xboole_0,k1_xboole_0,C_84)),k1_xboole_0)
      | ~ r2_hidden(C_84,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_394])).

tff(c_505,plain,(
    ! [C_93] :
      ( r2_hidden(k4_tarski(C_93,'#skF_4'(k1_xboole_0,k1_xboole_0,C_93)),k1_xboole_0)
      | ~ r2_hidden(C_93,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_408])).

tff(c_24,plain,(
    ! [A_21,B_22] : k1_relat_1('#skF_5'(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    ! [A_21,B_22] : v1_relat_1('#skF_5'(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_85,plain,(
    ! [A_21,B_22] :
      ( k1_relat_1('#skF_5'(A_21,B_22)) != k1_xboole_0
      | '#skF_5'(A_21,B_22) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_82])).

tff(c_90,plain,(
    ! [A_21,B_22] :
      ( k1_xboole_0 != A_21
      | '#skF_5'(A_21,B_22) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_85])).

tff(c_284,plain,(
    ! [A_68,B_69,D_70] :
      ( k1_funct_1('#skF_5'(A_68,B_69),D_70) = B_69
      | ~ r2_hidden(D_70,A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_293,plain,(
    ! [D_70,B_22,A_21] :
      ( k1_funct_1(k1_xboole_0,D_70) = B_22
      | ~ r2_hidden(D_70,A_21)
      | k1_xboole_0 != A_21 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_284])).

tff(c_608,plain,(
    ! [C_107] :
      ( k1_funct_1(k1_xboole_0,k4_tarski(C_107,'#skF_4'(k1_xboole_0,k1_xboole_0,C_107))) = '#skF_7'
      | ~ r2_hidden(C_107,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_505,c_293])).

tff(c_511,plain,(
    ! [C_93,B_22] :
      ( k1_funct_1(k1_xboole_0,k4_tarski(C_93,'#skF_4'(k1_xboole_0,k1_xboole_0,C_93))) = B_22
      | ~ r2_hidden(C_93,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_505,c_293])).

tff(c_611,plain,(
    ! [B_22,C_107] :
      ( B_22 = '#skF_7'
      | ~ r2_hidden(C_107,k1_xboole_0)
      | ~ r2_hidden(C_107,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_511])).

tff(c_862,plain,(
    ! [C_107] :
      ( ~ r2_hidden(C_107,k1_xboole_0)
      | ~ r2_hidden(C_107,k1_xboole_0) ) ),
    inference(splitLeft,[status(thm)],[c_611])).

tff(c_3436,plain,(
    ! [A_3534] :
      ( ~ r2_hidden('#skF_3'('#skF_6'(A_3534),k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_1'('#skF_6'(A_3534),k1_xboole_0),A_3534)
      | k1_xboole_0 = A_3534 ) ),
    inference(resolution,[status(thm)],[c_2249,c_862])).

tff(c_3464,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_1'('#skF_6'(A_28),k1_xboole_0),A_28)
      | k1_xboole_0 = A_28 ) ),
    inference(resolution,[status(thm)],[c_1013,c_3436])).

tff(c_2,plain,(
    ! [C_16,A_1] :
      ( r2_hidden(k4_tarski(C_16,'#skF_4'(A_1,k1_relat_1(A_1),C_16)),A_1)
      | ~ r2_hidden(C_16,k1_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_92,plain,(
    ! [A_28] :
      ( k1_xboole_0 != A_28
      | '#skF_6'(A_28) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_88])).

tff(c_405,plain,(
    ! [C_84,A_28] :
      ( r2_hidden(k4_tarski(C_84,'#skF_4'('#skF_6'(A_28),A_28,C_84)),'#skF_6'(A_28))
      | ~ r2_hidden(C_84,k1_relat_1('#skF_6'(A_28))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_394])).

tff(c_915,plain,(
    ! [C_907,A_908] :
      ( r2_hidden(k4_tarski(C_907,'#skF_4'('#skF_6'(A_908),A_908,C_907)),'#skF_6'(A_908))
      | ~ r2_hidden(C_907,A_908) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_405])).

tff(c_959,plain,(
    ! [C_907,A_28] :
      ( r2_hidden(k4_tarski(C_907,'#skF_4'('#skF_6'(A_28),A_28,C_907)),k1_xboole_0)
      | ~ r2_hidden(C_907,A_28)
      | k1_xboole_0 != A_28 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_915])).

tff(c_2321,plain,(
    ! [C_2151,A_2152] :
      ( r2_hidden(k4_tarski(C_2151,'#skF_4'('#skF_6'(A_2152),A_2152,C_2151)),k1_xboole_0)
      | ~ r2_hidden(C_2151,A_2152)
      | k1_xboole_0 != A_2152 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_915])).

tff(c_3839,plain,(
    ! [C_3980,A_3981] :
      ( ~ r2_hidden(k4_tarski(C_3980,'#skF_4'('#skF_6'(A_3981),A_3981,C_3980)),k1_xboole_0)
      | ~ r2_hidden(C_3980,A_3981)
      | k1_xboole_0 != A_3981 ) ),
    inference(resolution,[status(thm)],[c_2321,c_862])).

tff(c_3880,plain,(
    ! [C_4036,A_4037] :
      ( ~ r2_hidden(C_4036,A_4037)
      | k1_xboole_0 != A_4037 ) ),
    inference(resolution,[status(thm)],[c_959,c_3839])).

tff(c_3996,plain,(
    ! [A_4093,C_4094] :
      ( k1_xboole_0 != A_4093
      | ~ r2_hidden(C_4094,k1_relat_1(A_4093)) ) ),
    inference(resolution,[status(thm)],[c_2,c_3880])).

tff(c_4056,plain,(
    ! [A_4093] :
      ( k1_xboole_0 != A_4093
      | k1_relat_1(A_4093) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3464,c_3996])).

tff(c_39164,plain,(
    ! [A_4498,B_4499] :
      ( k1_xboole_0 != A_4498
      | r2_hidden('#skF_3'('#skF_6'(k1_relat_1(A_4498)),B_4499),B_4499)
      | k1_relat_1(A_4498) = B_4499 ) ),
    inference(resolution,[status(thm)],[c_1013,c_3996])).

tff(c_39397,plain,(
    ! [A_4093,B_4499] :
      ( k1_xboole_0 != A_4093
      | r2_hidden('#skF_3'('#skF_6'(k1_xboole_0),B_4499),B_4499)
      | k1_relat_1(A_4093) = B_4499
      | k1_xboole_0 != A_4093 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4056,c_39164])).

tff(c_50908,plain,(
    ! [A_4522] :
      ( k1_xboole_0 != A_4522
      | r2_hidden('#skF_3'(k1_xboole_0,'#skF_7'),'#skF_7')
      | k1_relat_1(A_4522) = '#skF_7'
      | k1_xboole_0 != A_4522 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_39397])).

tff(c_50911,plain,(
    ! [A_4522] :
      ( k1_xboole_0 != A_4522
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 != A_4522
      | r2_hidden('#skF_3'(k1_xboole_0,'#skF_7'),'#skF_7')
      | k1_xboole_0 != A_4522 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50908,c_4056])).

tff(c_52088,plain,(
    ! [A_4522] :
      ( k1_xboole_0 != A_4522
      | k1_xboole_0 != A_4522
      | r2_hidden('#skF_3'(k1_xboole_0,'#skF_7'),'#skF_7')
      | k1_xboole_0 != A_4522 ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_50911])).

tff(c_52098,plain,(
    ! [A_4522] :
      ( k1_xboole_0 != A_4522
      | k1_xboole_0 != A_4522
      | k1_xboole_0 != A_4522 ) ),
    inference(splitLeft,[status(thm)],[c_52088])).

tff(c_52105,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_52098])).

tff(c_52106,plain,(
    r2_hidden('#skF_3'(k1_xboole_0,'#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_52088])).

tff(c_26,plain,(
    ! [A_21,B_22] : v1_funct_1('#skF_5'(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    ! [A_28] : v1_funct_1('#skF_6'(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_71,plain,(
    ! [C_49,B_50] :
      ( C_49 = B_50
      | k1_relat_1(C_49) != '#skF_7'
      | k1_relat_1(B_50) != '#skF_7'
      | ~ v1_funct_1(C_49)
      | ~ v1_relat_1(C_49)
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_75,plain,(
    ! [B_50,A_28] :
      ( B_50 = '#skF_6'(A_28)
      | k1_relat_1('#skF_6'(A_28)) != '#skF_7'
      | k1_relat_1(B_50) != '#skF_7'
      | ~ v1_funct_1('#skF_6'(A_28))
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50) ) ),
    inference(resolution,[status(thm)],[c_36,c_71])).

tff(c_154,plain,(
    ! [B_54,A_55] :
      ( B_54 = '#skF_6'(A_55)
      | A_55 != '#skF_7'
      | k1_relat_1(B_54) != '#skF_7'
      | ~ v1_funct_1(B_54)
      | ~ v1_relat_1(B_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_75])).

tff(c_158,plain,(
    ! [A_55,A_21,B_22] :
      ( '#skF_6'(A_55) = '#skF_5'(A_21,B_22)
      | A_55 != '#skF_7'
      | k1_relat_1('#skF_5'(A_21,B_22)) != '#skF_7'
      | ~ v1_funct_1('#skF_5'(A_21,B_22)) ) ),
    inference(resolution,[status(thm)],[c_28,c_154])).

tff(c_320,plain,(
    ! [A_76,A_77,B_78] :
      ( '#skF_6'(A_76) = '#skF_5'(A_77,B_78)
      | A_76 != '#skF_7'
      | A_77 != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_158])).

tff(c_22,plain,(
    ! [A_21,B_22,D_27] :
      ( k1_funct_1('#skF_5'(A_21,B_22),D_27) = B_22
      | ~ r2_hidden(D_27,A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_332,plain,(
    ! [A_76,D_27,B_78,A_77] :
      ( k1_funct_1('#skF_6'(A_76),D_27) = B_78
      | ~ r2_hidden(D_27,A_77)
      | A_76 != '#skF_7'
      | A_77 != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_22])).

tff(c_53857,plain,(
    ! [A_9124] :
      ( k1_funct_1('#skF_6'(A_9124),'#skF_3'(k1_xboole_0,'#skF_7')) = '#skF_7'
      | A_9124 != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_52106,c_332])).

tff(c_52123,plain,(
    ! [A_76,B_78] :
      ( k1_funct_1('#skF_6'(A_76),'#skF_3'(k1_xboole_0,'#skF_7')) = B_78
      | A_76 != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_52106,c_332])).

tff(c_53860,plain,(
    ! [B_78,A_9124] :
      ( B_78 = '#skF_7'
      | A_9124 != '#skF_7'
      | A_9124 != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53857,c_52123])).

tff(c_55083,plain,(
    ! [A_9124] :
      ( A_9124 != '#skF_7'
      | A_9124 != '#skF_7' ) ),
    inference(splitLeft,[status(thm)],[c_53860])).

tff(c_55089,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_55083])).

tff(c_55091,plain,(
    ! [B_13734] : B_13734 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_53860])).

tff(c_14,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_56177,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_55091,c_14])).

tff(c_56211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_56177])).

tff(c_56233,plain,(
    ! [B_18399] : B_18399 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_611])).

tff(c_56336,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_56233,c_14])).

tff(c_56351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_56336])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:01:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.93/10.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.93/10.45  
% 18.93/10.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.93/10.45  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_6
% 18.93/10.45  
% 18.93/10.45  %Foreground sorts:
% 18.93/10.45  
% 18.93/10.45  
% 18.93/10.45  %Background operators:
% 18.93/10.45  
% 18.93/10.45  
% 18.93/10.45  %Foreground operators:
% 18.93/10.45  tff(np__1, type, np__1: $i).
% 18.93/10.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 18.93/10.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.93/10.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.93/10.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 18.93/10.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.93/10.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 18.93/10.45  tff('#skF_7', type, '#skF_7': $i).
% 18.93/10.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 18.93/10.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 18.93/10.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 18.93/10.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.93/10.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.93/10.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.93/10.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 18.93/10.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 18.93/10.45  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 18.93/10.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 18.93/10.45  tff('#skF_6', type, '#skF_6': $i > $i).
% 18.93/10.45  
% 18.93/10.46  tff(f_87, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 18.93/10.46  tff(f_68, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 18.93/10.46  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 18.93/10.46  tff(f_33, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 18.93/10.46  tff(f_36, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 18.93/10.46  tff(f_56, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 18.93/10.46  tff(c_38, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_87])).
% 18.93/10.46  tff(c_32, plain, (![A_28]: (k1_relat_1('#skF_6'(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_68])).
% 18.93/10.46  tff(c_36, plain, (![A_28]: (v1_relat_1('#skF_6'(A_28)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 18.93/10.46  tff(c_82, plain, (![A_51]: (k1_relat_1(A_51)!=k1_xboole_0 | k1_xboole_0=A_51 | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_44])).
% 18.93/10.46  tff(c_88, plain, (![A_28]: (k1_relat_1('#skF_6'(A_28))!=k1_xboole_0 | '#skF_6'(A_28)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_82])).
% 18.93/10.46  tff(c_93, plain, ('#skF_6'(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_88])).
% 18.93/10.46  tff(c_876, plain, (![A_866, B_867]: (r2_hidden(k4_tarski('#skF_1'(A_866, B_867), '#skF_2'(A_866, B_867)), A_866) | r2_hidden('#skF_3'(A_866, B_867), B_867) | k1_relat_1(A_866)=B_867)), inference(cnfTransformation, [status(thm)], [f_33])).
% 18.93/10.46  tff(c_4, plain, (![C_16, A_1, D_19]: (r2_hidden(C_16, k1_relat_1(A_1)) | ~r2_hidden(k4_tarski(C_16, D_19), A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 18.93/10.46  tff(c_976, plain, (![A_946, B_947]: (r2_hidden('#skF_1'(A_946, B_947), k1_relat_1(A_946)) | r2_hidden('#skF_3'(A_946, B_947), B_947) | k1_relat_1(A_946)=B_947)), inference(resolution, [status(thm)], [c_876, c_4])).
% 18.93/10.46  tff(c_1002, plain, (![A_28, B_947]: (r2_hidden('#skF_1'('#skF_6'(A_28), B_947), A_28) | r2_hidden('#skF_3'('#skF_6'(A_28), B_947), B_947) | k1_relat_1('#skF_6'(A_28))=B_947)), inference(superposition, [status(thm), theory('equality')], [c_32, c_976])).
% 18.93/10.46  tff(c_1013, plain, (![A_28, B_947]: (r2_hidden('#skF_1'('#skF_6'(A_28), B_947), A_28) | r2_hidden('#skF_3'('#skF_6'(A_28), B_947), B_947) | B_947=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1002])).
% 18.93/10.46  tff(c_2249, plain, (![A_2113, B_2114]: (r2_hidden('#skF_1'('#skF_6'(A_2113), B_2114), A_2113) | r2_hidden('#skF_3'('#skF_6'(A_2113), B_2114), B_2114) | B_2114=A_2113)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1002])).
% 18.93/10.46  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 18.93/10.46  tff(c_394, plain, (![C_84, A_85]: (r2_hidden(k4_tarski(C_84, '#skF_4'(A_85, k1_relat_1(A_85), C_84)), A_85) | ~r2_hidden(C_84, k1_relat_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 18.93/10.46  tff(c_408, plain, (![C_84]: (r2_hidden(k4_tarski(C_84, '#skF_4'(k1_xboole_0, k1_xboole_0, C_84)), k1_xboole_0) | ~r2_hidden(C_84, k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_394])).
% 18.93/10.46  tff(c_505, plain, (![C_93]: (r2_hidden(k4_tarski(C_93, '#skF_4'(k1_xboole_0, k1_xboole_0, C_93)), k1_xboole_0) | ~r2_hidden(C_93, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_408])).
% 18.93/10.46  tff(c_24, plain, (![A_21, B_22]: (k1_relat_1('#skF_5'(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_56])).
% 18.93/10.46  tff(c_28, plain, (![A_21, B_22]: (v1_relat_1('#skF_5'(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 18.93/10.46  tff(c_85, plain, (![A_21, B_22]: (k1_relat_1('#skF_5'(A_21, B_22))!=k1_xboole_0 | '#skF_5'(A_21, B_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_82])).
% 18.93/10.46  tff(c_90, plain, (![A_21, B_22]: (k1_xboole_0!=A_21 | '#skF_5'(A_21, B_22)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_85])).
% 18.93/10.46  tff(c_284, plain, (![A_68, B_69, D_70]: (k1_funct_1('#skF_5'(A_68, B_69), D_70)=B_69 | ~r2_hidden(D_70, A_68))), inference(cnfTransformation, [status(thm)], [f_56])).
% 18.93/10.46  tff(c_293, plain, (![D_70, B_22, A_21]: (k1_funct_1(k1_xboole_0, D_70)=B_22 | ~r2_hidden(D_70, A_21) | k1_xboole_0!=A_21)), inference(superposition, [status(thm), theory('equality')], [c_90, c_284])).
% 18.93/10.46  tff(c_608, plain, (![C_107]: (k1_funct_1(k1_xboole_0, k4_tarski(C_107, '#skF_4'(k1_xboole_0, k1_xboole_0, C_107)))='#skF_7' | ~r2_hidden(C_107, k1_xboole_0))), inference(resolution, [status(thm)], [c_505, c_293])).
% 18.93/10.46  tff(c_511, plain, (![C_93, B_22]: (k1_funct_1(k1_xboole_0, k4_tarski(C_93, '#skF_4'(k1_xboole_0, k1_xboole_0, C_93)))=B_22 | ~r2_hidden(C_93, k1_xboole_0))), inference(resolution, [status(thm)], [c_505, c_293])).
% 18.93/10.46  tff(c_611, plain, (![B_22, C_107]: (B_22='#skF_7' | ~r2_hidden(C_107, k1_xboole_0) | ~r2_hidden(C_107, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_608, c_511])).
% 18.93/10.46  tff(c_862, plain, (![C_107]: (~r2_hidden(C_107, k1_xboole_0) | ~r2_hidden(C_107, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_611])).
% 18.93/10.46  tff(c_3436, plain, (![A_3534]: (~r2_hidden('#skF_3'('#skF_6'(A_3534), k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_1'('#skF_6'(A_3534), k1_xboole_0), A_3534) | k1_xboole_0=A_3534)), inference(resolution, [status(thm)], [c_2249, c_862])).
% 18.93/10.46  tff(c_3464, plain, (![A_28]: (r2_hidden('#skF_1'('#skF_6'(A_28), k1_xboole_0), A_28) | k1_xboole_0=A_28)), inference(resolution, [status(thm)], [c_1013, c_3436])).
% 18.93/10.46  tff(c_2, plain, (![C_16, A_1]: (r2_hidden(k4_tarski(C_16, '#skF_4'(A_1, k1_relat_1(A_1), C_16)), A_1) | ~r2_hidden(C_16, k1_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 18.93/10.46  tff(c_92, plain, (![A_28]: (k1_xboole_0!=A_28 | '#skF_6'(A_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_88])).
% 18.93/10.46  tff(c_405, plain, (![C_84, A_28]: (r2_hidden(k4_tarski(C_84, '#skF_4'('#skF_6'(A_28), A_28, C_84)), '#skF_6'(A_28)) | ~r2_hidden(C_84, k1_relat_1('#skF_6'(A_28))))), inference(superposition, [status(thm), theory('equality')], [c_32, c_394])).
% 18.93/10.46  tff(c_915, plain, (![C_907, A_908]: (r2_hidden(k4_tarski(C_907, '#skF_4'('#skF_6'(A_908), A_908, C_907)), '#skF_6'(A_908)) | ~r2_hidden(C_907, A_908))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_405])).
% 18.93/10.46  tff(c_959, plain, (![C_907, A_28]: (r2_hidden(k4_tarski(C_907, '#skF_4'('#skF_6'(A_28), A_28, C_907)), k1_xboole_0) | ~r2_hidden(C_907, A_28) | k1_xboole_0!=A_28)), inference(superposition, [status(thm), theory('equality')], [c_92, c_915])).
% 18.93/10.46  tff(c_2321, plain, (![C_2151, A_2152]: (r2_hidden(k4_tarski(C_2151, '#skF_4'('#skF_6'(A_2152), A_2152, C_2151)), k1_xboole_0) | ~r2_hidden(C_2151, A_2152) | k1_xboole_0!=A_2152)), inference(superposition, [status(thm), theory('equality')], [c_92, c_915])).
% 18.93/10.46  tff(c_3839, plain, (![C_3980, A_3981]: (~r2_hidden(k4_tarski(C_3980, '#skF_4'('#skF_6'(A_3981), A_3981, C_3980)), k1_xboole_0) | ~r2_hidden(C_3980, A_3981) | k1_xboole_0!=A_3981)), inference(resolution, [status(thm)], [c_2321, c_862])).
% 18.93/10.46  tff(c_3880, plain, (![C_4036, A_4037]: (~r2_hidden(C_4036, A_4037) | k1_xboole_0!=A_4037)), inference(resolution, [status(thm)], [c_959, c_3839])).
% 18.93/10.46  tff(c_3996, plain, (![A_4093, C_4094]: (k1_xboole_0!=A_4093 | ~r2_hidden(C_4094, k1_relat_1(A_4093)))), inference(resolution, [status(thm)], [c_2, c_3880])).
% 18.93/10.46  tff(c_4056, plain, (![A_4093]: (k1_xboole_0!=A_4093 | k1_relat_1(A_4093)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3464, c_3996])).
% 18.93/10.46  tff(c_39164, plain, (![A_4498, B_4499]: (k1_xboole_0!=A_4498 | r2_hidden('#skF_3'('#skF_6'(k1_relat_1(A_4498)), B_4499), B_4499) | k1_relat_1(A_4498)=B_4499)), inference(resolution, [status(thm)], [c_1013, c_3996])).
% 18.93/10.46  tff(c_39397, plain, (![A_4093, B_4499]: (k1_xboole_0!=A_4093 | r2_hidden('#skF_3'('#skF_6'(k1_xboole_0), B_4499), B_4499) | k1_relat_1(A_4093)=B_4499 | k1_xboole_0!=A_4093)), inference(superposition, [status(thm), theory('equality')], [c_4056, c_39164])).
% 18.93/10.46  tff(c_50908, plain, (![A_4522]: (k1_xboole_0!=A_4522 | r2_hidden('#skF_3'(k1_xboole_0, '#skF_7'), '#skF_7') | k1_relat_1(A_4522)='#skF_7' | k1_xboole_0!=A_4522)), inference(demodulation, [status(thm), theory('equality')], [c_93, c_39397])).
% 18.93/10.46  tff(c_50911, plain, (![A_4522]: (k1_xboole_0!=A_4522 | k1_xboole_0='#skF_7' | k1_xboole_0!=A_4522 | r2_hidden('#skF_3'(k1_xboole_0, '#skF_7'), '#skF_7') | k1_xboole_0!=A_4522)), inference(superposition, [status(thm), theory('equality')], [c_50908, c_4056])).
% 18.93/10.46  tff(c_52088, plain, (![A_4522]: (k1_xboole_0!=A_4522 | k1_xboole_0!=A_4522 | r2_hidden('#skF_3'(k1_xboole_0, '#skF_7'), '#skF_7') | k1_xboole_0!=A_4522)), inference(negUnitSimplification, [status(thm)], [c_38, c_50911])).
% 18.93/10.46  tff(c_52098, plain, (![A_4522]: (k1_xboole_0!=A_4522 | k1_xboole_0!=A_4522 | k1_xboole_0!=A_4522)), inference(splitLeft, [status(thm)], [c_52088])).
% 18.93/10.46  tff(c_52105, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_52098])).
% 18.93/10.46  tff(c_52106, plain, (r2_hidden('#skF_3'(k1_xboole_0, '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_52088])).
% 18.93/10.46  tff(c_26, plain, (![A_21, B_22]: (v1_funct_1('#skF_5'(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 18.93/10.46  tff(c_34, plain, (![A_28]: (v1_funct_1('#skF_6'(A_28)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 18.93/10.46  tff(c_71, plain, (![C_49, B_50]: (C_49=B_50 | k1_relat_1(C_49)!='#skF_7' | k1_relat_1(B_50)!='#skF_7' | ~v1_funct_1(C_49) | ~v1_relat_1(C_49) | ~v1_funct_1(B_50) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_87])).
% 18.93/10.46  tff(c_75, plain, (![B_50, A_28]: (B_50='#skF_6'(A_28) | k1_relat_1('#skF_6'(A_28))!='#skF_7' | k1_relat_1(B_50)!='#skF_7' | ~v1_funct_1('#skF_6'(A_28)) | ~v1_funct_1(B_50) | ~v1_relat_1(B_50))), inference(resolution, [status(thm)], [c_36, c_71])).
% 18.93/10.46  tff(c_154, plain, (![B_54, A_55]: (B_54='#skF_6'(A_55) | A_55!='#skF_7' | k1_relat_1(B_54)!='#skF_7' | ~v1_funct_1(B_54) | ~v1_relat_1(B_54))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_75])).
% 18.93/10.46  tff(c_158, plain, (![A_55, A_21, B_22]: ('#skF_6'(A_55)='#skF_5'(A_21, B_22) | A_55!='#skF_7' | k1_relat_1('#skF_5'(A_21, B_22))!='#skF_7' | ~v1_funct_1('#skF_5'(A_21, B_22)))), inference(resolution, [status(thm)], [c_28, c_154])).
% 18.93/10.46  tff(c_320, plain, (![A_76, A_77, B_78]: ('#skF_6'(A_76)='#skF_5'(A_77, B_78) | A_76!='#skF_7' | A_77!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_158])).
% 18.93/10.46  tff(c_22, plain, (![A_21, B_22, D_27]: (k1_funct_1('#skF_5'(A_21, B_22), D_27)=B_22 | ~r2_hidden(D_27, A_21))), inference(cnfTransformation, [status(thm)], [f_56])).
% 18.93/10.46  tff(c_332, plain, (![A_76, D_27, B_78, A_77]: (k1_funct_1('#skF_6'(A_76), D_27)=B_78 | ~r2_hidden(D_27, A_77) | A_76!='#skF_7' | A_77!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_320, c_22])).
% 18.93/10.46  tff(c_53857, plain, (![A_9124]: (k1_funct_1('#skF_6'(A_9124), '#skF_3'(k1_xboole_0, '#skF_7'))='#skF_7' | A_9124!='#skF_7')), inference(resolution, [status(thm)], [c_52106, c_332])).
% 18.93/10.46  tff(c_52123, plain, (![A_76, B_78]: (k1_funct_1('#skF_6'(A_76), '#skF_3'(k1_xboole_0, '#skF_7'))=B_78 | A_76!='#skF_7')), inference(resolution, [status(thm)], [c_52106, c_332])).
% 18.93/10.46  tff(c_53860, plain, (![B_78, A_9124]: (B_78='#skF_7' | A_9124!='#skF_7' | A_9124!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_53857, c_52123])).
% 18.93/10.46  tff(c_55083, plain, (![A_9124]: (A_9124!='#skF_7' | A_9124!='#skF_7')), inference(splitLeft, [status(thm)], [c_53860])).
% 18.93/10.46  tff(c_55089, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_55083])).
% 18.93/10.46  tff(c_55091, plain, (![B_13734]: (B_13734='#skF_7')), inference(splitRight, [status(thm)], [c_53860])).
% 18.93/10.46  tff(c_14, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 18.93/10.46  tff(c_56177, plain, (k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_55091, c_14])).
% 18.93/10.46  tff(c_56211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_56177])).
% 18.93/10.46  tff(c_56233, plain, (![B_18399]: (B_18399='#skF_7')), inference(splitRight, [status(thm)], [c_611])).
% 18.93/10.46  tff(c_56336, plain, (k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_56233, c_14])).
% 18.93/10.46  tff(c_56351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_56336])).
% 18.93/10.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.93/10.46  
% 18.93/10.46  Inference rules
% 18.93/10.46  ----------------------
% 18.93/10.46  #Ref     : 22
% 18.93/10.46  #Sup     : 15484
% 18.93/10.46  #Fact    : 0
% 18.93/10.46  #Define  : 0
% 18.93/10.46  #Split   : 18
% 18.93/10.46  #Chain   : 0
% 18.93/10.46  #Close   : 0
% 18.93/10.46  
% 18.93/10.46  Ordering : KBO
% 18.93/10.46  
% 18.93/10.46  Simplification rules
% 18.93/10.46  ----------------------
% 18.93/10.46  #Subsume      : 9114
% 18.93/10.46  #Demod        : 3067
% 18.93/10.46  #Tautology    : 941
% 18.93/10.46  #SimpNegUnit  : 226
% 18.93/10.46  #BackRed      : 158
% 18.93/10.46  
% 18.93/10.46  #Partial instantiations: 9503
% 18.93/10.46  #Strategies tried      : 1
% 18.93/10.47  
% 18.93/10.47  Timing (in seconds)
% 18.93/10.47  ----------------------
% 18.93/10.47  Preprocessing        : 0.31
% 18.93/10.47  Parsing              : 0.17
% 18.93/10.47  CNF conversion       : 0.02
% 18.93/10.47  Main loop            : 9.31
% 18.93/10.47  Inferencing          : 1.11
% 18.93/10.47  Reduction            : 2.01
% 18.93/10.47  Demodulation         : 1.46
% 18.93/10.47  BG Simplification    : 0.12
% 18.93/10.47  Subsumption          : 5.78
% 18.93/10.47  Abstraction          : 0.19
% 18.93/10.47  MUC search           : 0.00
% 18.93/10.47  Cooper               : 0.00
% 18.93/10.47  Total                : 9.65
% 18.93/10.47  Index Insertion      : 0.00
% 18.93/10.47  Index Deletion       : 0.00
% 18.93/10.47  Index Matching       : 0.00
% 18.93/10.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
