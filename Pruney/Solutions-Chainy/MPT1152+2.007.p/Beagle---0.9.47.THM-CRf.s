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
% DateTime   : Thu Dec  3 10:19:28 EST 2020

% Result     : Theorem 8.64s
% Output     : CNFRefutation 8.72s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 844 expanded)
%              Number of leaves         :   38 ( 322 expanded)
%              Depth                    :   22
%              Number of atoms          :  356 (2717 expanded)
%              Number of equality atoms :   57 ( 454 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_mcart_1 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(a_2_1_orders_2,type,(
    a_2_1_orders_2: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_152,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_orders_2(A,B) = a_2_1_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_138,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_1_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_64,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

tff(c_109,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_1'(A_68,B_69),A_68)
      | r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_114,plain,(
    ! [A_68] : r1_tarski(A_68,A_68) ),
    inference(resolution,[status(thm)],[c_109,c_4])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_56,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_54,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_52,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_50,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_34,plain,(
    ! [A_39] :
      ( l1_struct_0(A_39)
      | ~ l1_orders_2(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_61,plain,(
    ! [A_55] :
      ( u1_struct_0(A_55) = k2_struct_0(A_55)
      | ~ l1_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_67,plain,(
    ! [A_58] :
      ( u1_struct_0(A_58) = k2_struct_0(A_58)
      | ~ l1_orders_2(A_58) ) ),
    inference(resolution,[status(thm)],[c_34,c_61])).

tff(c_71,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_67])).

tff(c_282,plain,(
    ! [A_135,B_136] :
      ( k2_orders_2(A_135,B_136) = a_2_1_orders_2(A_135,B_136)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_orders_2(A_135)
      | ~ v5_orders_2(A_135)
      | ~ v4_orders_2(A_135)
      | ~ v3_orders_2(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_297,plain,(
    ! [B_136] :
      ( k2_orders_2('#skF_5',B_136) = a_2_1_orders_2('#skF_5',B_136)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_282])).

tff(c_302,plain,(
    ! [B_136] :
      ( k2_orders_2('#skF_5',B_136) = a_2_1_orders_2('#skF_5',B_136)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_297])).

tff(c_304,plain,(
    ! [B_137] :
      ( k2_orders_2('#skF_5',B_137) = a_2_1_orders_2('#skF_5',B_137)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_302])).

tff(c_320,plain,(
    ! [A_138] :
      ( k2_orders_2('#skF_5',A_138) = a_2_1_orders_2('#skF_5',A_138)
      | ~ r1_tarski(A_138,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_12,c_304])).

tff(c_335,plain,(
    k2_orders_2('#skF_5',k2_struct_0('#skF_5')) = a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_114,c_320])).

tff(c_48,plain,(
    k2_orders_2('#skF_5',k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_336,plain,(
    a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_48])).

tff(c_81,plain,(
    ! [A_61] :
      ( ~ v1_xboole_0(u1_struct_0(A_61))
      | ~ l1_struct_0(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_84,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_81])).

tff(c_85,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_84])).

tff(c_86,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_90,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_86])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_90])).

tff(c_95,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_371,plain,(
    ! [A_156,B_157,C_158] :
      ( '#skF_3'(A_156,B_157,C_158) = A_156
      | ~ r2_hidden(A_156,a_2_1_orders_2(B_157,C_158))
      | ~ m1_subset_1(C_158,k1_zfmisc_1(u1_struct_0(B_157)))
      | ~ l1_orders_2(B_157)
      | ~ v5_orders_2(B_157)
      | ~ v4_orders_2(B_157)
      | ~ v3_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_7729,plain,(
    ! [B_673,C_674,B_675] :
      ( '#skF_3'('#skF_1'(a_2_1_orders_2(B_673,C_674),B_675),B_673,C_674) = '#skF_1'(a_2_1_orders_2(B_673,C_674),B_675)
      | ~ m1_subset_1(C_674,k1_zfmisc_1(u1_struct_0(B_673)))
      | ~ l1_orders_2(B_673)
      | ~ v5_orders_2(B_673)
      | ~ v4_orders_2(B_673)
      | ~ v3_orders_2(B_673)
      | v2_struct_0(B_673)
      | r1_tarski(a_2_1_orders_2(B_673,C_674),B_675) ) ),
    inference(resolution,[status(thm)],[c_6,c_371])).

tff(c_7767,plain,(
    ! [C_674,B_675] :
      ( '#skF_3'('#skF_1'(a_2_1_orders_2('#skF_5',C_674),B_675),'#skF_5',C_674) = '#skF_1'(a_2_1_orders_2('#skF_5',C_674),B_675)
      | ~ m1_subset_1(C_674,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | r1_tarski(a_2_1_orders_2('#skF_5',C_674),B_675) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_7729])).

tff(c_7781,plain,(
    ! [C_674,B_675] :
      ( '#skF_3'('#skF_1'(a_2_1_orders_2('#skF_5',C_674),B_675),'#skF_5',C_674) = '#skF_1'(a_2_1_orders_2('#skF_5',C_674),B_675)
      | ~ m1_subset_1(C_674,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | r1_tarski(a_2_1_orders_2('#skF_5',C_674),B_675) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_7767])).

tff(c_7828,plain,(
    ! [C_679,B_680] :
      ( '#skF_3'('#skF_1'(a_2_1_orders_2('#skF_5',C_679),B_680),'#skF_5',C_679) = '#skF_1'(a_2_1_orders_2('#skF_5',C_679),B_680)
      | ~ m1_subset_1(C_679,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | r1_tarski(a_2_1_orders_2('#skF_5',C_679),B_680) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_7781])).

tff(c_8673,plain,(
    ! [A_723,B_724] :
      ( '#skF_3'('#skF_1'(a_2_1_orders_2('#skF_5',A_723),B_724),'#skF_5',A_723) = '#skF_1'(a_2_1_orders_2('#skF_5',A_723),B_724)
      | r1_tarski(a_2_1_orders_2('#skF_5',A_723),B_724)
      | ~ r1_tarski(A_723,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_12,c_7828])).

tff(c_46,plain,(
    ! [A_40,B_41,C_42] :
      ( m1_subset_1('#skF_3'(A_40,B_41,C_42),u1_struct_0(B_41))
      | ~ r2_hidden(A_40,a_2_1_orders_2(B_41,C_42))
      | ~ m1_subset_1(C_42,k1_zfmisc_1(u1_struct_0(B_41)))
      | ~ l1_orders_2(B_41)
      | ~ v5_orders_2(B_41)
      | ~ v4_orders_2(B_41)
      | ~ v3_orders_2(B_41)
      | v2_struct_0(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_8692,plain,(
    ! [A_723,B_724] :
      ( m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_5',A_723),B_724),u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_5',A_723),B_724),a_2_1_orders_2('#skF_5',A_723))
      | ~ m1_subset_1(A_723,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | r1_tarski(a_2_1_orders_2('#skF_5',A_723),B_724)
      | ~ r1_tarski(A_723,k2_struct_0('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8673,c_46])).

tff(c_8701,plain,(
    ! [A_723,B_724] :
      ( m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_5',A_723),B_724),k2_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_5',A_723),B_724),a_2_1_orders_2('#skF_5',A_723))
      | ~ m1_subset_1(A_723,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | r1_tarski(a_2_1_orders_2('#skF_5',A_723),B_724)
      | ~ r1_tarski(A_723,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_71,c_71,c_8692])).

tff(c_8761,plain,(
    ! [A_727,B_728] :
      ( m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_5',A_727),B_728),k2_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_5',A_727),B_728),a_2_1_orders_2('#skF_5',A_727))
      | ~ m1_subset_1(A_727,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | r1_tarski(a_2_1_orders_2('#skF_5',A_727),B_728)
      | ~ r1_tarski(A_727,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_8701])).

tff(c_8979,plain,(
    ! [A_745,B_746] :
      ( m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_5',A_745),B_746),k2_struct_0('#skF_5'))
      | ~ m1_subset_1(A_745,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r1_tarski(A_745,k2_struct_0('#skF_5'))
      | r1_tarski(a_2_1_orders_2('#skF_5',A_745),B_746) ) ),
    inference(resolution,[status(thm)],[c_6,c_8761])).

tff(c_103,plain,(
    ! [A_66,B_67] :
      ( r2_hidden(A_66,B_67)
      | v1_xboole_0(B_67)
      | ~ m1_subset_1(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_108,plain,(
    ! [A_1,B_67] :
      ( r1_tarski(A_1,B_67)
      | v1_xboole_0(B_67)
      | ~ m1_subset_1('#skF_1'(A_1,B_67),B_67) ) ),
    inference(resolution,[status(thm)],[c_103,c_4])).

tff(c_8985,plain,(
    ! [A_745] :
      ( v1_xboole_0(k2_struct_0('#skF_5'))
      | ~ m1_subset_1(A_745,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r1_tarski(A_745,k2_struct_0('#skF_5'))
      | r1_tarski(a_2_1_orders_2('#skF_5',A_745),k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_8979,c_108])).

tff(c_8990,plain,(
    ! [A_747] :
      ( ~ m1_subset_1(A_747,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r1_tarski(A_747,k2_struct_0('#skF_5'))
      | r1_tarski(a_2_1_orders_2('#skF_5',A_747),k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_8985])).

tff(c_16,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_2'(A_13),A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_116,plain,(
    ! [C_71,B_72,A_73] :
      ( r2_hidden(C_71,B_72)
      | ~ r2_hidden(C_71,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_126,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_2'(A_74),B_75)
      | ~ r1_tarski(A_74,B_75)
      | k1_xboole_0 = A_74 ) ),
    inference(resolution,[status(thm)],[c_16,c_116])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_129,plain,(
    ! [A_74,B_2,B_75] :
      ( r2_hidden('#skF_2'(A_74),B_2)
      | ~ r1_tarski(B_75,B_2)
      | ~ r1_tarski(A_74,B_75)
      | k1_xboole_0 = A_74 ) ),
    inference(resolution,[status(thm)],[c_126,c_2])).

tff(c_9368,plain,(
    ! [A_756,A_757] :
      ( r2_hidden('#skF_2'(A_756),k2_struct_0('#skF_5'))
      | ~ r1_tarski(A_756,a_2_1_orders_2('#skF_5',A_757))
      | k1_xboole_0 = A_756
      | ~ m1_subset_1(A_757,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r1_tarski(A_757,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_8990,c_129])).

tff(c_9420,plain,(
    ! [A_757] :
      ( r2_hidden('#skF_2'(a_2_1_orders_2('#skF_5',A_757)),k2_struct_0('#skF_5'))
      | a_2_1_orders_2('#skF_5',A_757) = k1_xboole_0
      | ~ m1_subset_1(A_757,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r1_tarski(A_757,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_114,c_9368])).

tff(c_6965,plain,(
    ! [B_635,C_636] :
      ( '#skF_3'('#skF_2'(a_2_1_orders_2(B_635,C_636)),B_635,C_636) = '#skF_2'(a_2_1_orders_2(B_635,C_636))
      | ~ m1_subset_1(C_636,k1_zfmisc_1(u1_struct_0(B_635)))
      | ~ l1_orders_2(B_635)
      | ~ v5_orders_2(B_635)
      | ~ v4_orders_2(B_635)
      | ~ v3_orders_2(B_635)
      | v2_struct_0(B_635)
      | a_2_1_orders_2(B_635,C_636) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_371])).

tff(c_7003,plain,(
    ! [C_636] :
      ( '#skF_3'('#skF_2'(a_2_1_orders_2('#skF_5',C_636)),'#skF_5',C_636) = '#skF_2'(a_2_1_orders_2('#skF_5',C_636))
      | ~ m1_subset_1(C_636,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | a_2_1_orders_2('#skF_5',C_636) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_6965])).

tff(c_7017,plain,(
    ! [C_636] :
      ( '#skF_3'('#skF_2'(a_2_1_orders_2('#skF_5',C_636)),'#skF_5',C_636) = '#skF_2'(a_2_1_orders_2('#skF_5',C_636))
      | ~ m1_subset_1(C_636,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | a_2_1_orders_2('#skF_5',C_636) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_7003])).

tff(c_7206,plain,(
    ! [C_640] :
      ( '#skF_3'('#skF_2'(a_2_1_orders_2('#skF_5',C_640)),'#skF_5',C_640) = '#skF_2'(a_2_1_orders_2('#skF_5',C_640))
      | ~ m1_subset_1(C_640,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | a_2_1_orders_2('#skF_5',C_640) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_7017])).

tff(c_7254,plain,(
    ! [A_8] :
      ( '#skF_3'('#skF_2'(a_2_1_orders_2('#skF_5',A_8)),'#skF_5',A_8) = '#skF_2'(a_2_1_orders_2('#skF_5',A_8))
      | a_2_1_orders_2('#skF_5',A_8) = k1_xboole_0
      | ~ r1_tarski(A_8,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_12,c_7206])).

tff(c_5387,plain,(
    ! [B_522,A_523,C_524,E_525] :
      ( r2_orders_2(B_522,'#skF_3'(A_523,B_522,C_524),E_525)
      | ~ r2_hidden(E_525,C_524)
      | ~ m1_subset_1(E_525,u1_struct_0(B_522))
      | ~ r2_hidden(A_523,a_2_1_orders_2(B_522,C_524))
      | ~ m1_subset_1(C_524,k1_zfmisc_1(u1_struct_0(B_522)))
      | ~ l1_orders_2(B_522)
      | ~ v5_orders_2(B_522)
      | ~ v4_orders_2(B_522)
      | ~ v3_orders_2(B_522)
      | v2_struct_0(B_522) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_7491,plain,(
    ! [B_655,A_656,A_657,E_658] :
      ( r2_orders_2(B_655,'#skF_3'(A_656,B_655,A_657),E_658)
      | ~ r2_hidden(E_658,A_657)
      | ~ m1_subset_1(E_658,u1_struct_0(B_655))
      | ~ r2_hidden(A_656,a_2_1_orders_2(B_655,A_657))
      | ~ l1_orders_2(B_655)
      | ~ v5_orders_2(B_655)
      | ~ v4_orders_2(B_655)
      | ~ v3_orders_2(B_655)
      | v2_struct_0(B_655)
      | ~ r1_tarski(A_657,u1_struct_0(B_655)) ) ),
    inference(resolution,[status(thm)],[c_12,c_5387])).

tff(c_7502,plain,(
    ! [A_8,E_658] :
      ( r2_orders_2('#skF_5','#skF_2'(a_2_1_orders_2('#skF_5',A_8)),E_658)
      | ~ r2_hidden(E_658,A_8)
      | ~ m1_subset_1(E_658,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_1_orders_2('#skF_5',A_8)),a_2_1_orders_2('#skF_5',A_8))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r1_tarski(A_8,u1_struct_0('#skF_5'))
      | a_2_1_orders_2('#skF_5',A_8) = k1_xboole_0
      | ~ r1_tarski(A_8,k2_struct_0('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7254,c_7491])).

tff(c_7507,plain,(
    ! [A_8,E_658] :
      ( r2_orders_2('#skF_5','#skF_2'(a_2_1_orders_2('#skF_5',A_8)),E_658)
      | ~ r2_hidden(E_658,A_8)
      | ~ m1_subset_1(E_658,k2_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_1_orders_2('#skF_5',A_8)),a_2_1_orders_2('#skF_5',A_8))
      | v2_struct_0('#skF_5')
      | a_2_1_orders_2('#skF_5',A_8) = k1_xboole_0
      | ~ r1_tarski(A_8,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_56,c_54,c_52,c_50,c_71,c_7502])).

tff(c_8121,plain,(
    ! [A_706,E_707] :
      ( r2_orders_2('#skF_5','#skF_2'(a_2_1_orders_2('#skF_5',A_706)),E_707)
      | ~ r2_hidden(E_707,A_706)
      | ~ m1_subset_1(E_707,k2_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_1_orders_2('#skF_5',A_706)),a_2_1_orders_2('#skF_5',A_706))
      | a_2_1_orders_2('#skF_5',A_706) = k1_xboole_0
      | ~ r1_tarski(A_706,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_7507])).

tff(c_9504,plain,(
    ! [A_762,E_763] :
      ( r2_orders_2('#skF_5','#skF_2'(a_2_1_orders_2('#skF_5',A_762)),E_763)
      | ~ r2_hidden(E_763,A_762)
      | ~ m1_subset_1(E_763,k2_struct_0('#skF_5'))
      | ~ r1_tarski(A_762,k2_struct_0('#skF_5'))
      | a_2_1_orders_2('#skF_5',A_762) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_8121])).

tff(c_28,plain,(
    ! [A_29,C_35] :
      ( ~ r2_orders_2(A_29,C_35,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_29))
      | ~ l1_orders_2(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_9512,plain,(
    ! [A_762] :
      ( ~ m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5',A_762)),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ r2_hidden('#skF_2'(a_2_1_orders_2('#skF_5',A_762)),A_762)
      | ~ m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5',A_762)),k2_struct_0('#skF_5'))
      | ~ r1_tarski(A_762,k2_struct_0('#skF_5'))
      | a_2_1_orders_2('#skF_5',A_762) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9504,c_28])).

tff(c_9523,plain,(
    ! [A_764] :
      ( ~ r2_hidden('#skF_2'(a_2_1_orders_2('#skF_5',A_764)),A_764)
      | ~ m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5',A_764)),k2_struct_0('#skF_5'))
      | ~ r1_tarski(A_764,k2_struct_0('#skF_5'))
      | a_2_1_orders_2('#skF_5',A_764) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_71,c_9512])).

tff(c_9526,plain,
    ( ~ m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_9420,c_9523])).

tff(c_9535,plain,
    ( ~ m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_9526])).

tff(c_9536,plain,
    ( ~ m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_9535])).

tff(c_9539,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_9536])).

tff(c_9542,plain,(
    ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_12,c_9539])).

tff(c_9546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_9542])).

tff(c_9548,plain,(
    m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_9536])).

tff(c_125,plain,(
    ! [A_13,B_72] :
      ( r2_hidden('#skF_2'(A_13),B_72)
      | ~ r1_tarski(A_13,B_72)
      | k1_xboole_0 = A_13 ) ),
    inference(resolution,[status(thm)],[c_16,c_116])).

tff(c_7271,plain,(
    ! [A_644] :
      ( '#skF_3'('#skF_2'(a_2_1_orders_2('#skF_5',A_644)),'#skF_5',A_644) = '#skF_2'(a_2_1_orders_2('#skF_5',A_644))
      | a_2_1_orders_2('#skF_5',A_644) = k1_xboole_0
      | ~ r1_tarski(A_644,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_12,c_7206])).

tff(c_7287,plain,(
    ! [A_644] :
      ( m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5',A_644)),u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_1_orders_2('#skF_5',A_644)),a_2_1_orders_2('#skF_5',A_644))
      | ~ m1_subset_1(A_644,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | a_2_1_orders_2('#skF_5',A_644) = k1_xboole_0
      | ~ r1_tarski(A_644,k2_struct_0('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7271,c_46])).

tff(c_7293,plain,(
    ! [A_644] :
      ( m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5',A_644)),k2_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_1_orders_2('#skF_5',A_644)),a_2_1_orders_2('#skF_5',A_644))
      | ~ m1_subset_1(A_644,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | a_2_1_orders_2('#skF_5',A_644) = k1_xboole_0
      | ~ r1_tarski(A_644,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_71,c_71,c_7287])).

tff(c_7609,plain,(
    ! [A_666] :
      ( m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5',A_666)),k2_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_1_orders_2('#skF_5',A_666)),a_2_1_orders_2('#skF_5',A_666))
      | ~ m1_subset_1(A_666,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | a_2_1_orders_2('#skF_5',A_666) = k1_xboole_0
      | ~ r1_tarski(A_666,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_7293])).

tff(c_7612,plain,(
    ! [A_666] :
      ( m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5',A_666)),k2_struct_0('#skF_5'))
      | ~ m1_subset_1(A_666,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r1_tarski(A_666,k2_struct_0('#skF_5'))
      | ~ r1_tarski(a_2_1_orders_2('#skF_5',A_666),a_2_1_orders_2('#skF_5',A_666))
      | a_2_1_orders_2('#skF_5',A_666) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_125,c_7609])).

tff(c_7621,plain,(
    ! [A_666] :
      ( m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5',A_666)),k2_struct_0('#skF_5'))
      | ~ m1_subset_1(A_666,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r1_tarski(A_666,k2_struct_0('#skF_5'))
      | a_2_1_orders_2('#skF_5',A_666) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_7612])).

tff(c_9547,plain,(
    ~ m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_9536])).

tff(c_9643,plain,
    ( ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_5'))
    | a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7621,c_9547])).

tff(c_9649,plain,(
    a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_9548,c_9643])).

tff(c_9651,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_9649])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:34:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.64/3.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.72/3.22  
% 8.72/3.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.72/3.22  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_mcart_1 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1
% 8.72/3.22  
% 8.72/3.22  %Foreground sorts:
% 8.72/3.22  
% 8.72/3.22  
% 8.72/3.22  %Background operators:
% 8.72/3.22  
% 8.72/3.22  
% 8.72/3.22  %Foreground operators:
% 8.72/3.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.72/3.22  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 8.72/3.22  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.72/3.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.72/3.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.72/3.22  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 8.72/3.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.72/3.22  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 8.72/3.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.72/3.22  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 8.72/3.22  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 8.72/3.22  tff('#skF_5', type, '#skF_5': $i).
% 8.72/3.22  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 8.72/3.22  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 8.72/3.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.72/3.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.72/3.22  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 8.72/3.22  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 8.72/3.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.72/3.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.72/3.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.72/3.22  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 8.72/3.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.72/3.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.72/3.22  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 8.72/3.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.72/3.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.72/3.22  
% 8.72/3.24  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.72/3.24  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.72/3.24  tff(f_152, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_orders_2)).
% 8.72/3.24  tff(f_111, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 8.72/3.24  tff(f_68, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 8.72/3.24  tff(f_107, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 8.72/3.24  tff(f_76, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 8.72/3.24  tff(f_138, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 8.72/3.24  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 8.72/3.24  tff(f_64, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 8.72/3.24  tff(f_91, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 8.72/3.24  tff(c_109, plain, (![A_68, B_69]: (r2_hidden('#skF_1'(A_68, B_69), A_68) | r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.72/3.24  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.72/3.24  tff(c_114, plain, (![A_68]: (r1_tarski(A_68, A_68))), inference(resolution, [status(thm)], [c_109, c_4])).
% 8.72/3.24  tff(c_12, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.72/3.24  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.72/3.24  tff(c_56, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.72/3.24  tff(c_54, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.72/3.24  tff(c_52, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.72/3.24  tff(c_50, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.72/3.24  tff(c_34, plain, (![A_39]: (l1_struct_0(A_39) | ~l1_orders_2(A_39))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.72/3.24  tff(c_61, plain, (![A_55]: (u1_struct_0(A_55)=k2_struct_0(A_55) | ~l1_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.72/3.24  tff(c_67, plain, (![A_58]: (u1_struct_0(A_58)=k2_struct_0(A_58) | ~l1_orders_2(A_58))), inference(resolution, [status(thm)], [c_34, c_61])).
% 8.72/3.24  tff(c_71, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_67])).
% 8.72/3.24  tff(c_282, plain, (![A_135, B_136]: (k2_orders_2(A_135, B_136)=a_2_1_orders_2(A_135, B_136) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_orders_2(A_135) | ~v5_orders_2(A_135) | ~v4_orders_2(A_135) | ~v3_orders_2(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.72/3.24  tff(c_297, plain, (![B_136]: (k2_orders_2('#skF_5', B_136)=a_2_1_orders_2('#skF_5', B_136) | ~m1_subset_1(B_136, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_282])).
% 8.72/3.24  tff(c_302, plain, (![B_136]: (k2_orders_2('#skF_5', B_136)=a_2_1_orders_2('#skF_5', B_136) | ~m1_subset_1(B_136, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_297])).
% 8.72/3.24  tff(c_304, plain, (![B_137]: (k2_orders_2('#skF_5', B_137)=a_2_1_orders_2('#skF_5', B_137) | ~m1_subset_1(B_137, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_302])).
% 8.72/3.24  tff(c_320, plain, (![A_138]: (k2_orders_2('#skF_5', A_138)=a_2_1_orders_2('#skF_5', A_138) | ~r1_tarski(A_138, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_12, c_304])).
% 8.72/3.24  tff(c_335, plain, (k2_orders_2('#skF_5', k2_struct_0('#skF_5'))=a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_114, c_320])).
% 8.72/3.24  tff(c_48, plain, (k2_orders_2('#skF_5', k2_struct_0('#skF_5'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.72/3.24  tff(c_336, plain, (a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_335, c_48])).
% 8.72/3.24  tff(c_81, plain, (![A_61]: (~v1_xboole_0(u1_struct_0(A_61)) | ~l1_struct_0(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.72/3.24  tff(c_84, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_71, c_81])).
% 8.72/3.24  tff(c_85, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_84])).
% 8.72/3.24  tff(c_86, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_85])).
% 8.72/3.24  tff(c_90, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_34, c_86])).
% 8.72/3.24  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_90])).
% 8.72/3.24  tff(c_95, plain, (~v1_xboole_0(k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_85])).
% 8.72/3.24  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.72/3.24  tff(c_371, plain, (![A_156, B_157, C_158]: ('#skF_3'(A_156, B_157, C_158)=A_156 | ~r2_hidden(A_156, a_2_1_orders_2(B_157, C_158)) | ~m1_subset_1(C_158, k1_zfmisc_1(u1_struct_0(B_157))) | ~l1_orders_2(B_157) | ~v5_orders_2(B_157) | ~v4_orders_2(B_157) | ~v3_orders_2(B_157) | v2_struct_0(B_157))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.72/3.24  tff(c_7729, plain, (![B_673, C_674, B_675]: ('#skF_3'('#skF_1'(a_2_1_orders_2(B_673, C_674), B_675), B_673, C_674)='#skF_1'(a_2_1_orders_2(B_673, C_674), B_675) | ~m1_subset_1(C_674, k1_zfmisc_1(u1_struct_0(B_673))) | ~l1_orders_2(B_673) | ~v5_orders_2(B_673) | ~v4_orders_2(B_673) | ~v3_orders_2(B_673) | v2_struct_0(B_673) | r1_tarski(a_2_1_orders_2(B_673, C_674), B_675))), inference(resolution, [status(thm)], [c_6, c_371])).
% 8.72/3.24  tff(c_7767, plain, (![C_674, B_675]: ('#skF_3'('#skF_1'(a_2_1_orders_2('#skF_5', C_674), B_675), '#skF_5', C_674)='#skF_1'(a_2_1_orders_2('#skF_5', C_674), B_675) | ~m1_subset_1(C_674, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | r1_tarski(a_2_1_orders_2('#skF_5', C_674), B_675))), inference(superposition, [status(thm), theory('equality')], [c_71, c_7729])).
% 8.72/3.24  tff(c_7781, plain, (![C_674, B_675]: ('#skF_3'('#skF_1'(a_2_1_orders_2('#skF_5', C_674), B_675), '#skF_5', C_674)='#skF_1'(a_2_1_orders_2('#skF_5', C_674), B_675) | ~m1_subset_1(C_674, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | r1_tarski(a_2_1_orders_2('#skF_5', C_674), B_675))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_7767])).
% 8.72/3.24  tff(c_7828, plain, (![C_679, B_680]: ('#skF_3'('#skF_1'(a_2_1_orders_2('#skF_5', C_679), B_680), '#skF_5', C_679)='#skF_1'(a_2_1_orders_2('#skF_5', C_679), B_680) | ~m1_subset_1(C_679, k1_zfmisc_1(k2_struct_0('#skF_5'))) | r1_tarski(a_2_1_orders_2('#skF_5', C_679), B_680))), inference(negUnitSimplification, [status(thm)], [c_58, c_7781])).
% 8.72/3.24  tff(c_8673, plain, (![A_723, B_724]: ('#skF_3'('#skF_1'(a_2_1_orders_2('#skF_5', A_723), B_724), '#skF_5', A_723)='#skF_1'(a_2_1_orders_2('#skF_5', A_723), B_724) | r1_tarski(a_2_1_orders_2('#skF_5', A_723), B_724) | ~r1_tarski(A_723, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_12, c_7828])).
% 8.72/3.24  tff(c_46, plain, (![A_40, B_41, C_42]: (m1_subset_1('#skF_3'(A_40, B_41, C_42), u1_struct_0(B_41)) | ~r2_hidden(A_40, a_2_1_orders_2(B_41, C_42)) | ~m1_subset_1(C_42, k1_zfmisc_1(u1_struct_0(B_41))) | ~l1_orders_2(B_41) | ~v5_orders_2(B_41) | ~v4_orders_2(B_41) | ~v3_orders_2(B_41) | v2_struct_0(B_41))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.72/3.24  tff(c_8692, plain, (![A_723, B_724]: (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_5', A_723), B_724), u1_struct_0('#skF_5')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_5', A_723), B_724), a_2_1_orders_2('#skF_5', A_723)) | ~m1_subset_1(A_723, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | r1_tarski(a_2_1_orders_2('#skF_5', A_723), B_724) | ~r1_tarski(A_723, k2_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_8673, c_46])).
% 8.72/3.24  tff(c_8701, plain, (![A_723, B_724]: (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_5', A_723), B_724), k2_struct_0('#skF_5')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_5', A_723), B_724), a_2_1_orders_2('#skF_5', A_723)) | ~m1_subset_1(A_723, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | r1_tarski(a_2_1_orders_2('#skF_5', A_723), B_724) | ~r1_tarski(A_723, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_71, c_71, c_8692])).
% 8.72/3.24  tff(c_8761, plain, (![A_727, B_728]: (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_5', A_727), B_728), k2_struct_0('#skF_5')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_5', A_727), B_728), a_2_1_orders_2('#skF_5', A_727)) | ~m1_subset_1(A_727, k1_zfmisc_1(k2_struct_0('#skF_5'))) | r1_tarski(a_2_1_orders_2('#skF_5', A_727), B_728) | ~r1_tarski(A_727, k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_8701])).
% 8.72/3.24  tff(c_8979, plain, (![A_745, B_746]: (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_5', A_745), B_746), k2_struct_0('#skF_5')) | ~m1_subset_1(A_745, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~r1_tarski(A_745, k2_struct_0('#skF_5')) | r1_tarski(a_2_1_orders_2('#skF_5', A_745), B_746))), inference(resolution, [status(thm)], [c_6, c_8761])).
% 8.72/3.24  tff(c_103, plain, (![A_66, B_67]: (r2_hidden(A_66, B_67) | v1_xboole_0(B_67) | ~m1_subset_1(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.72/3.24  tff(c_108, plain, (![A_1, B_67]: (r1_tarski(A_1, B_67) | v1_xboole_0(B_67) | ~m1_subset_1('#skF_1'(A_1, B_67), B_67))), inference(resolution, [status(thm)], [c_103, c_4])).
% 8.72/3.24  tff(c_8985, plain, (![A_745]: (v1_xboole_0(k2_struct_0('#skF_5')) | ~m1_subset_1(A_745, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~r1_tarski(A_745, k2_struct_0('#skF_5')) | r1_tarski(a_2_1_orders_2('#skF_5', A_745), k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_8979, c_108])).
% 8.72/3.24  tff(c_8990, plain, (![A_747]: (~m1_subset_1(A_747, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~r1_tarski(A_747, k2_struct_0('#skF_5')) | r1_tarski(a_2_1_orders_2('#skF_5', A_747), k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_95, c_8985])).
% 8.72/3.24  tff(c_16, plain, (![A_13]: (r2_hidden('#skF_2'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.72/3.24  tff(c_116, plain, (![C_71, B_72, A_73]: (r2_hidden(C_71, B_72) | ~r2_hidden(C_71, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.72/3.24  tff(c_126, plain, (![A_74, B_75]: (r2_hidden('#skF_2'(A_74), B_75) | ~r1_tarski(A_74, B_75) | k1_xboole_0=A_74)), inference(resolution, [status(thm)], [c_16, c_116])).
% 8.72/3.24  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.72/3.24  tff(c_129, plain, (![A_74, B_2, B_75]: (r2_hidden('#skF_2'(A_74), B_2) | ~r1_tarski(B_75, B_2) | ~r1_tarski(A_74, B_75) | k1_xboole_0=A_74)), inference(resolution, [status(thm)], [c_126, c_2])).
% 8.72/3.24  tff(c_9368, plain, (![A_756, A_757]: (r2_hidden('#skF_2'(A_756), k2_struct_0('#skF_5')) | ~r1_tarski(A_756, a_2_1_orders_2('#skF_5', A_757)) | k1_xboole_0=A_756 | ~m1_subset_1(A_757, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~r1_tarski(A_757, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_8990, c_129])).
% 8.72/3.24  tff(c_9420, plain, (![A_757]: (r2_hidden('#skF_2'(a_2_1_orders_2('#skF_5', A_757)), k2_struct_0('#skF_5')) | a_2_1_orders_2('#skF_5', A_757)=k1_xboole_0 | ~m1_subset_1(A_757, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~r1_tarski(A_757, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_114, c_9368])).
% 8.72/3.24  tff(c_6965, plain, (![B_635, C_636]: ('#skF_3'('#skF_2'(a_2_1_orders_2(B_635, C_636)), B_635, C_636)='#skF_2'(a_2_1_orders_2(B_635, C_636)) | ~m1_subset_1(C_636, k1_zfmisc_1(u1_struct_0(B_635))) | ~l1_orders_2(B_635) | ~v5_orders_2(B_635) | ~v4_orders_2(B_635) | ~v3_orders_2(B_635) | v2_struct_0(B_635) | a_2_1_orders_2(B_635, C_636)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_371])).
% 8.72/3.24  tff(c_7003, plain, (![C_636]: ('#skF_3'('#skF_2'(a_2_1_orders_2('#skF_5', C_636)), '#skF_5', C_636)='#skF_2'(a_2_1_orders_2('#skF_5', C_636)) | ~m1_subset_1(C_636, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | a_2_1_orders_2('#skF_5', C_636)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_71, c_6965])).
% 8.72/3.24  tff(c_7017, plain, (![C_636]: ('#skF_3'('#skF_2'(a_2_1_orders_2('#skF_5', C_636)), '#skF_5', C_636)='#skF_2'(a_2_1_orders_2('#skF_5', C_636)) | ~m1_subset_1(C_636, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | a_2_1_orders_2('#skF_5', C_636)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_7003])).
% 8.72/3.24  tff(c_7206, plain, (![C_640]: ('#skF_3'('#skF_2'(a_2_1_orders_2('#skF_5', C_640)), '#skF_5', C_640)='#skF_2'(a_2_1_orders_2('#skF_5', C_640)) | ~m1_subset_1(C_640, k1_zfmisc_1(k2_struct_0('#skF_5'))) | a_2_1_orders_2('#skF_5', C_640)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_58, c_7017])).
% 8.72/3.24  tff(c_7254, plain, (![A_8]: ('#skF_3'('#skF_2'(a_2_1_orders_2('#skF_5', A_8)), '#skF_5', A_8)='#skF_2'(a_2_1_orders_2('#skF_5', A_8)) | a_2_1_orders_2('#skF_5', A_8)=k1_xboole_0 | ~r1_tarski(A_8, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_12, c_7206])).
% 8.72/3.24  tff(c_5387, plain, (![B_522, A_523, C_524, E_525]: (r2_orders_2(B_522, '#skF_3'(A_523, B_522, C_524), E_525) | ~r2_hidden(E_525, C_524) | ~m1_subset_1(E_525, u1_struct_0(B_522)) | ~r2_hidden(A_523, a_2_1_orders_2(B_522, C_524)) | ~m1_subset_1(C_524, k1_zfmisc_1(u1_struct_0(B_522))) | ~l1_orders_2(B_522) | ~v5_orders_2(B_522) | ~v4_orders_2(B_522) | ~v3_orders_2(B_522) | v2_struct_0(B_522))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.72/3.24  tff(c_7491, plain, (![B_655, A_656, A_657, E_658]: (r2_orders_2(B_655, '#skF_3'(A_656, B_655, A_657), E_658) | ~r2_hidden(E_658, A_657) | ~m1_subset_1(E_658, u1_struct_0(B_655)) | ~r2_hidden(A_656, a_2_1_orders_2(B_655, A_657)) | ~l1_orders_2(B_655) | ~v5_orders_2(B_655) | ~v4_orders_2(B_655) | ~v3_orders_2(B_655) | v2_struct_0(B_655) | ~r1_tarski(A_657, u1_struct_0(B_655)))), inference(resolution, [status(thm)], [c_12, c_5387])).
% 8.72/3.24  tff(c_7502, plain, (![A_8, E_658]: (r2_orders_2('#skF_5', '#skF_2'(a_2_1_orders_2('#skF_5', A_8)), E_658) | ~r2_hidden(E_658, A_8) | ~m1_subset_1(E_658, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_1_orders_2('#skF_5', A_8)), a_2_1_orders_2('#skF_5', A_8)) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r1_tarski(A_8, u1_struct_0('#skF_5')) | a_2_1_orders_2('#skF_5', A_8)=k1_xboole_0 | ~r1_tarski(A_8, k2_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_7254, c_7491])).
% 8.72/3.24  tff(c_7507, plain, (![A_8, E_658]: (r2_orders_2('#skF_5', '#skF_2'(a_2_1_orders_2('#skF_5', A_8)), E_658) | ~r2_hidden(E_658, A_8) | ~m1_subset_1(E_658, k2_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_1_orders_2('#skF_5', A_8)), a_2_1_orders_2('#skF_5', A_8)) | v2_struct_0('#skF_5') | a_2_1_orders_2('#skF_5', A_8)=k1_xboole_0 | ~r1_tarski(A_8, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_56, c_54, c_52, c_50, c_71, c_7502])).
% 8.72/3.24  tff(c_8121, plain, (![A_706, E_707]: (r2_orders_2('#skF_5', '#skF_2'(a_2_1_orders_2('#skF_5', A_706)), E_707) | ~r2_hidden(E_707, A_706) | ~m1_subset_1(E_707, k2_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_1_orders_2('#skF_5', A_706)), a_2_1_orders_2('#skF_5', A_706)) | a_2_1_orders_2('#skF_5', A_706)=k1_xboole_0 | ~r1_tarski(A_706, k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_7507])).
% 8.72/3.24  tff(c_9504, plain, (![A_762, E_763]: (r2_orders_2('#skF_5', '#skF_2'(a_2_1_orders_2('#skF_5', A_762)), E_763) | ~r2_hidden(E_763, A_762) | ~m1_subset_1(E_763, k2_struct_0('#skF_5')) | ~r1_tarski(A_762, k2_struct_0('#skF_5')) | a_2_1_orders_2('#skF_5', A_762)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_8121])).
% 8.72/3.24  tff(c_28, plain, (![A_29, C_35]: (~r2_orders_2(A_29, C_35, C_35) | ~m1_subset_1(C_35, u1_struct_0(A_29)) | ~l1_orders_2(A_29))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.72/3.24  tff(c_9512, plain, (![A_762]: (~m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5', A_762)), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~r2_hidden('#skF_2'(a_2_1_orders_2('#skF_5', A_762)), A_762) | ~m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5', A_762)), k2_struct_0('#skF_5')) | ~r1_tarski(A_762, k2_struct_0('#skF_5')) | a_2_1_orders_2('#skF_5', A_762)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9504, c_28])).
% 8.72/3.24  tff(c_9523, plain, (![A_764]: (~r2_hidden('#skF_2'(a_2_1_orders_2('#skF_5', A_764)), A_764) | ~m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5', A_764)), k2_struct_0('#skF_5')) | ~r1_tarski(A_764, k2_struct_0('#skF_5')) | a_2_1_orders_2('#skF_5', A_764)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_71, c_9512])).
% 8.72/3.24  tff(c_9526, plain, (~m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0 | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_9420, c_9523])).
% 8.72/3.24  tff(c_9535, plain, (~m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0 | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_9526])).
% 8.72/3.24  tff(c_9536, plain, (~m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_336, c_9535])).
% 8.72/3.24  tff(c_9539, plain, (~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_9536])).
% 8.72/3.24  tff(c_9542, plain, (~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_9539])).
% 8.72/3.24  tff(c_9546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_9542])).
% 8.72/3.24  tff(c_9548, plain, (m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_9536])).
% 8.72/3.24  tff(c_125, plain, (![A_13, B_72]: (r2_hidden('#skF_2'(A_13), B_72) | ~r1_tarski(A_13, B_72) | k1_xboole_0=A_13)), inference(resolution, [status(thm)], [c_16, c_116])).
% 8.72/3.24  tff(c_7271, plain, (![A_644]: ('#skF_3'('#skF_2'(a_2_1_orders_2('#skF_5', A_644)), '#skF_5', A_644)='#skF_2'(a_2_1_orders_2('#skF_5', A_644)) | a_2_1_orders_2('#skF_5', A_644)=k1_xboole_0 | ~r1_tarski(A_644, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_12, c_7206])).
% 8.72/3.24  tff(c_7287, plain, (![A_644]: (m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5', A_644)), u1_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_1_orders_2('#skF_5', A_644)), a_2_1_orders_2('#skF_5', A_644)) | ~m1_subset_1(A_644, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | a_2_1_orders_2('#skF_5', A_644)=k1_xboole_0 | ~r1_tarski(A_644, k2_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_7271, c_46])).
% 8.72/3.24  tff(c_7293, plain, (![A_644]: (m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5', A_644)), k2_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_1_orders_2('#skF_5', A_644)), a_2_1_orders_2('#skF_5', A_644)) | ~m1_subset_1(A_644, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | a_2_1_orders_2('#skF_5', A_644)=k1_xboole_0 | ~r1_tarski(A_644, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_71, c_71, c_7287])).
% 8.72/3.24  tff(c_7609, plain, (![A_666]: (m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5', A_666)), k2_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_1_orders_2('#skF_5', A_666)), a_2_1_orders_2('#skF_5', A_666)) | ~m1_subset_1(A_666, k1_zfmisc_1(k2_struct_0('#skF_5'))) | a_2_1_orders_2('#skF_5', A_666)=k1_xboole_0 | ~r1_tarski(A_666, k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_7293])).
% 8.72/3.24  tff(c_7612, plain, (![A_666]: (m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5', A_666)), k2_struct_0('#skF_5')) | ~m1_subset_1(A_666, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~r1_tarski(A_666, k2_struct_0('#skF_5')) | ~r1_tarski(a_2_1_orders_2('#skF_5', A_666), a_2_1_orders_2('#skF_5', A_666)) | a_2_1_orders_2('#skF_5', A_666)=k1_xboole_0)), inference(resolution, [status(thm)], [c_125, c_7609])).
% 8.72/3.24  tff(c_7621, plain, (![A_666]: (m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5', A_666)), k2_struct_0('#skF_5')) | ~m1_subset_1(A_666, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~r1_tarski(A_666, k2_struct_0('#skF_5')) | a_2_1_orders_2('#skF_5', A_666)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_114, c_7612])).
% 8.72/3.24  tff(c_9547, plain, (~m1_subset_1('#skF_2'(a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_9536])).
% 8.72/3.24  tff(c_9643, plain, (~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_5')) | a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_7621, c_9547])).
% 8.72/3.24  tff(c_9649, plain, (a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_114, c_9548, c_9643])).
% 8.72/3.24  tff(c_9651, plain, $false, inference(negUnitSimplification, [status(thm)], [c_336, c_9649])).
% 8.72/3.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.72/3.24  
% 8.72/3.24  Inference rules
% 8.72/3.24  ----------------------
% 8.72/3.24  #Ref     : 0
% 8.72/3.24  #Sup     : 2218
% 8.72/3.24  #Fact    : 0
% 8.72/3.24  #Define  : 0
% 8.72/3.24  #Split   : 9
% 8.72/3.24  #Chain   : 0
% 8.72/3.24  #Close   : 0
% 8.72/3.24  
% 8.72/3.24  Ordering : KBO
% 8.72/3.24  
% 8.72/3.24  Simplification rules
% 8.72/3.24  ----------------------
% 8.72/3.24  #Subsume      : 248
% 8.72/3.24  #Demod        : 901
% 8.72/3.24  #Tautology    : 207
% 8.72/3.24  #SimpNegUnit  : 117
% 8.72/3.24  #BackRed      : 45
% 8.72/3.24  
% 8.72/3.24  #Partial instantiations: 0
% 8.72/3.24  #Strategies tried      : 1
% 8.72/3.24  
% 8.72/3.24  Timing (in seconds)
% 8.72/3.24  ----------------------
% 8.72/3.25  Preprocessing        : 0.32
% 8.72/3.25  Parsing              : 0.16
% 8.72/3.25  CNF conversion       : 0.02
% 8.72/3.25  Main loop            : 2.08
% 8.72/3.25  Inferencing          : 0.59
% 8.72/3.25  Reduction            : 0.52
% 8.72/3.25  Demodulation         : 0.33
% 8.72/3.25  BG Simplification    : 0.10
% 8.72/3.25  Subsumption          : 0.71
% 8.72/3.25  Abstraction          : 0.12
% 8.72/3.25  MUC search           : 0.00
% 8.72/3.25  Cooper               : 0.00
% 8.72/3.25  Total                : 2.45
% 8.72/3.25  Index Insertion      : 0.00
% 8.72/3.25  Index Deletion       : 0.00
% 8.72/3.25  Index Matching       : 0.00
% 8.72/3.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
