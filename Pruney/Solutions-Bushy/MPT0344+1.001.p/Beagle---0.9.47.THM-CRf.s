%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0344+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:08 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 252 expanded)
%              Number of leaves         :   16 (  83 expanded)
%              Depth                    :   14
%              Number of atoms          :  131 ( 642 expanded)
%              Number of equality atoms :   10 (  41 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_37,plain,(
    ! [B_19,A_20] :
      ( m1_subset_1(B_19,A_20)
      | ~ v1_xboole_0(B_19)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_30,plain,(
    ! [C_18] :
      ( ~ r2_hidden(C_18,'#skF_3')
      | ~ m1_subset_1(C_18,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_35,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_30])).

tff(c_36,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_35])).

tff(c_41,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_3'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_37,c_36])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_41])).

tff(c_63,plain,(
    ! [B_25,A_26] :
      ( m1_subset_1(B_25,A_26)
      | ~ r2_hidden(B_25,A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_71,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_63])).

tff(c_53,plain,(
    ! [B_23,A_24] :
      ( r2_hidden(B_23,A_24)
      | ~ m1_subset_1(B_23,A_24)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [C_13] :
      ( ~ r2_hidden(C_13,'#skF_3')
      | ~ m1_subset_1(C_13,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_61,plain,(
    ! [B_23] :
      ( ~ m1_subset_1(B_23,'#skF_2')
      | ~ m1_subset_1(B_23,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_53,c_18])).

tff(c_78,plain,(
    ! [B_28] :
      ( ~ m1_subset_1(B_28,'#skF_2')
      | ~ m1_subset_1(B_28,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_82,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_2'),'#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_71,c_78])).

tff(c_89,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_82])).

tff(c_94,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_89])).

tff(c_95,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r2_hidden(B_6,A_5)
      | ~ m1_subset_1(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_96,plain,(
    ! [C_29,A_30,B_31] :
      ( r2_hidden(C_29,A_30)
      | ~ r2_hidden(C_29,B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_136,plain,(
    ! [B_36,A_37,A_38] :
      ( r2_hidden(B_36,A_37)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(A_37))
      | ~ m1_subset_1(B_36,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_8,c_96])).

tff(c_144,plain,(
    ! [B_36] :
      ( r2_hidden(B_36,'#skF_2')
      | ~ m1_subset_1(B_36,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_136])).

tff(c_150,plain,(
    ! [B_39] :
      ( r2_hidden(B_39,'#skF_2')
      | ~ m1_subset_1(B_39,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_144])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_155,plain,(
    ! [B_39] :
      ( m1_subset_1(B_39,'#skF_2')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(B_39,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_150,c_6])).

tff(c_164,plain,(
    ! [B_40] :
      ( m1_subset_1(B_40,'#skF_2')
      | ~ m1_subset_1(B_40,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_155])).

tff(c_77,plain,(
    ! [B_23] :
      ( ~ m1_subset_1(B_23,'#skF_2')
      | ~ m1_subset_1(B_23,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_177,plain,(
    ! [B_41] : ~ m1_subset_1(B_41,'#skF_3') ),
    inference(resolution,[status(thm)],[c_164,c_77])).

tff(c_181,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_177])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_181])).

tff(c_191,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_16,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_194,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_191,c_16])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_194])).

tff(c_199,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_202,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_199,c_16])).

tff(c_206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_202])).

tff(c_208,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_212,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_208,c_16])).

tff(c_214,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_20])).

tff(c_245,plain,(
    ! [B_48,A_49] :
      ( r2_hidden(B_48,A_49)
      | ~ m1_subset_1(B_48,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_257,plain,(
    ! [B_48] :
      ( ~ m1_subset_1(B_48,'#skF_2')
      | ~ m1_subset_1(B_48,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_245,c_18])).

tff(c_260,plain,(
    ! [B_50] :
      ( ~ m1_subset_1(B_50,'#skF_2')
      | ~ m1_subset_1(B_50,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_268,plain,(
    ! [B_6] :
      ( ~ m1_subset_1(B_6,'#skF_3')
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_10,c_260])).

tff(c_274,plain,(
    ! [B_51] :
      ( ~ m1_subset_1(B_51,'#skF_3')
      | ~ v1_xboole_0(B_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_268])).

tff(c_284,plain,(
    ! [B_6] :
      ( ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_274])).

tff(c_292,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_284])).

tff(c_285,plain,(
    ! [C_52,A_53,B_54] :
      ( r2_hidden(C_52,A_53)
      | ~ r2_hidden(C_52,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_293,plain,(
    ! [A_55,A_56] :
      ( r2_hidden('#skF_1'(A_55),A_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(A_56))
      | v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_4,c_285])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_323,plain,(
    ! [A_58,A_59] :
      ( ~ v1_xboole_0(A_58)
      | ~ m1_subset_1(A_59,k1_zfmisc_1(A_58))
      | v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_293,c_2])).

tff(c_334,plain,
    ( ~ v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_323])).

tff(c_339,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_334])).

tff(c_341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_292,c_339])).

tff(c_343,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_213,plain,(
    ! [A_11] :
      ( A_11 = '#skF_2'
      | ~ v1_xboole_0(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_16])).

tff(c_346,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_343,c_213])).

tff(c_350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_346])).

%------------------------------------------------------------------------------
