%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1432+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:55 EST 2020

% Result     : Theorem 4.69s
% Output     : CNFRefutation 4.78s
% Verified   : 
% Statistics : Number of formulae       :  213 (1581 expanded)
%              Number of leaves         :   26 ( 587 expanded)
%              Depth                    :   14
%              Number of atoms          :  733 (9502 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r3_binop_1 > r2_binop_1 > r1_binop_1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k6_filter_1 > k1_domain_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_domain_1,type,(
    k1_domain_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r3_binop_1,type,(
    r3_binop_1: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(r1_binop_1,type,(
    r1_binop_1: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k6_filter_1,type,(
    k6_filter_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r2_binop_1,type,(
    r2_binop_1: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_169,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,A)
               => ! [D] :
                    ( m1_subset_1(D,B)
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,k2_zfmisc_1(A,A),A)
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,k2_zfmisc_1(B,B),B)
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
                           => ( ( r3_binop_1(A,C,E)
                                & r3_binop_1(B,D,F) )
                            <=> r3_binop_1(k2_zfmisc_1(A,B),k1_domain_1(A,B,C,D),k6_filter_1(A,B,E,F)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_filter_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ! [C] :
          ( ( v1_funct_1(C)
            & v1_funct_2(C,k2_zfmisc_1(A,A),A)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
         => ( r3_binop_1(A,B,C)
          <=> ( r1_binop_1(A,B,C)
              & r2_binop_1(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_binop_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,k2_zfmisc_1(A,A),A)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A)))
        & v1_funct_1(D)
        & v1_funct_2(D,k2_zfmisc_1(B,B),B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
     => ( v1_funct_1(k6_filter_1(A,B,C,D))
        & v1_funct_2(k6_filter_1(A,B,C,D),k2_zfmisc_1(k2_zfmisc_1(A,B),k2_zfmisc_1(A,B)),k2_zfmisc_1(A,B))
        & m1_subset_1(k6_filter_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),k2_zfmisc_1(A,B)),k2_zfmisc_1(A,B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_filter_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(C,A)
        & m1_subset_1(D,B) )
     => m1_subset_1(k1_domain_1(A,B,C,D),k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_domain_1)).

tff(f_102,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( m1_subset_1(C,A)
             => ! [D] :
                  ( m1_subset_1(D,B)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,k2_zfmisc_1(A,A),A)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,k2_zfmisc_1(B,B),B)
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
                         => ( ( r1_binop_1(A,C,E)
                              & r1_binop_1(B,D,F) )
                          <=> r1_binop_1(k2_zfmisc_1(A,B),k1_domain_1(A,B,C,D),k6_filter_1(A,B,E,F)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_filter_1)).

tff(f_135,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( m1_subset_1(C,A)
             => ! [D] :
                  ( m1_subset_1(D,B)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,k2_zfmisc_1(A,A),A)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,k2_zfmisc_1(B,B),B)
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
                         => ( ( r2_binop_1(A,C,E)
                              & r2_binop_1(B,D,F) )
                          <=> r2_binop_1(k2_zfmisc_1(A,B),k1_domain_1(A,B,C,D),k6_filter_1(A,B,E,F)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_filter_1)).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_42,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_40,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_36,plain,(
    v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_32,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_30,plain,(
    v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_28,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_377,plain,(
    ! [A_297,B_298,C_299] :
      ( r3_binop_1(A_297,B_298,C_299)
      | ~ r2_binop_1(A_297,B_298,C_299)
      | ~ r1_binop_1(A_297,B_298,C_299)
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_297,A_297),A_297)))
      | ~ v1_funct_2(C_299,k2_zfmisc_1(A_297,A_297),A_297)
      | ~ v1_funct_1(C_299)
      | ~ m1_subset_1(B_298,A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_379,plain,(
    ! [B_298] :
      ( r3_binop_1('#skF_2',B_298,'#skF_6')
      | ~ r2_binop_1('#skF_2',B_298,'#skF_6')
      | ~ r1_binop_1('#skF_2',B_298,'#skF_6')
      | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(B_298,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_377])).

tff(c_388,plain,(
    ! [B_300] :
      ( r3_binop_1('#skF_2',B_300,'#skF_6')
      | ~ r2_binop_1('#skF_2',B_300,'#skF_6')
      | ~ r1_binop_1('#skF_2',B_300,'#skF_6')
      | ~ m1_subset_1(B_300,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_379])).

tff(c_73,plain,(
    ! [A_206,B_207,C_208] :
      ( r3_binop_1(A_206,B_207,C_208)
      | ~ r2_binop_1(A_206,B_207,C_208)
      | ~ r1_binop_1(A_206,B_207,C_208)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_206,A_206),A_206)))
      | ~ v1_funct_2(C_208,k2_zfmisc_1(A_206,A_206),A_206)
      | ~ v1_funct_1(C_208)
      | ~ m1_subset_1(B_207,A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_77,plain,(
    ! [B_207] :
      ( r3_binop_1('#skF_1',B_207,'#skF_5')
      | ~ r2_binop_1('#skF_1',B_207,'#skF_5')
      | ~ r1_binop_1('#skF_1',B_207,'#skF_5')
      | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(B_207,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_73])).

tff(c_95,plain,(
    ! [B_210] :
      ( r3_binop_1('#skF_1',B_210,'#skF_5')
      | ~ r2_binop_1('#skF_1',B_210,'#skF_5')
      | ~ r1_binop_1('#skF_1',B_210,'#skF_5')
      | ~ m1_subset_1(B_210,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_77])).

tff(c_56,plain,
    ( r3_binop_1('#skF_2','#skF_4','#skF_6')
    | r3_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_59,plain,(
    r3_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_48,plain,
    ( ~ r3_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ r3_binop_1('#skF_2','#skF_4','#skF_6')
    | ~ r3_binop_1('#skF_1','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_63,plain,
    ( ~ r3_binop_1('#skF_2','#skF_4','#skF_6')
    | ~ r3_binop_1('#skF_1','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_48])).

tff(c_64,plain,(
    ~ r3_binop_1('#skF_1','#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_102,plain,
    ( ~ r2_binop_1('#skF_1','#skF_3','#skF_5')
    | ~ r1_binop_1('#skF_1','#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_95,c_64])).

tff(c_111,plain,
    ( ~ r2_binop_1('#skF_1','#skF_3','#skF_5')
    | ~ r1_binop_1('#skF_1','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_102])).

tff(c_112,plain,(
    ~ r1_binop_1('#skF_1','#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( m1_subset_1(k6_filter_1(A_9,B_10,C_11,D_12),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),k2_zfmisc_1(A_9,B_10)),k2_zfmisc_1(A_9,B_10))))
      | ~ m1_subset_1(D_12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_10,B_10),B_10)))
      | ~ v1_funct_2(D_12,k2_zfmisc_1(B_10,B_10),B_10)
      | ~ v1_funct_1(D_12)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9,A_9),A_9)))
      | ~ v1_funct_2(C_11,k2_zfmisc_1(A_9,A_9),A_9)
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( v1_funct_2(k6_filter_1(A_9,B_10,C_11,D_12),k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),k2_zfmisc_1(A_9,B_10)),k2_zfmisc_1(A_9,B_10))
      | ~ m1_subset_1(D_12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_10,B_10),B_10)))
      | ~ v1_funct_2(D_12,k2_zfmisc_1(B_10,B_10),B_10)
      | ~ v1_funct_1(D_12)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9,A_9),A_9)))
      | ~ v1_funct_2(C_11,k2_zfmisc_1(A_9,A_9),A_9)
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7,D_8] :
      ( m1_subset_1(k1_domain_1(A_5,B_6,C_7,D_8),k2_zfmisc_1(A_5,B_6))
      | ~ m1_subset_1(D_8,B_6)
      | ~ m1_subset_1(C_7,A_5)
      | v1_xboole_0(B_6)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_113,plain,(
    ! [A_211,B_212,C_213,D_214] :
      ( v1_funct_1(k6_filter_1(A_211,B_212,C_213,D_214))
      | ~ m1_subset_1(D_214,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_212,B_212),B_212)))
      | ~ v1_funct_2(D_214,k2_zfmisc_1(B_212,B_212),B_212)
      | ~ v1_funct_1(D_214)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_211,A_211),A_211)))
      | ~ v1_funct_2(C_213,k2_zfmisc_1(A_211,A_211),A_211)
      | ~ v1_funct_1(C_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_115,plain,(
    ! [A_211,C_213] :
      ( v1_funct_1(k6_filter_1(A_211,'#skF_2',C_213,'#skF_6'))
      | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_211,A_211),A_211)))
      | ~ v1_funct_2(C_213,k2_zfmisc_1(A_211,A_211),A_211)
      | ~ v1_funct_1(C_213) ) ),
    inference(resolution,[status(thm)],[c_28,c_113])).

tff(c_124,plain,(
    ! [A_215,C_216] :
      ( v1_funct_1(k6_filter_1(A_215,'#skF_2',C_216,'#skF_6'))
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_215,A_215),A_215)))
      | ~ v1_funct_2(C_216,k2_zfmisc_1(A_215,A_215),A_215)
      | ~ v1_funct_1(C_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_115])).

tff(c_130,plain,
    ( v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_124])).

tff(c_136,plain,(
    v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_130])).

tff(c_65,plain,(
    ! [A_200,B_201,C_202] :
      ( r2_binop_1(A_200,B_201,C_202)
      | ~ r3_binop_1(A_200,B_201,C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_200,A_200),A_200)))
      | ~ v1_funct_2(C_202,k2_zfmisc_1(A_200,A_200),A_200)
      | ~ v1_funct_1(C_202)
      | ~ m1_subset_1(B_201,A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_68,plain,
    ( r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_59,c_65])).

tff(c_171,plain,
    ( r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_68])).

tff(c_172,plain,(
    ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_175,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_172])).

tff(c_178,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_175])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_178])).

tff(c_182,plain,(
    m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_69,plain,(
    ! [A_203,B_204,C_205] :
      ( r1_binop_1(A_203,B_204,C_205)
      | ~ r3_binop_1(A_203,B_204,C_205)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_203,A_203),A_203)))
      | ~ v1_funct_2(C_205,k2_zfmisc_1(A_203,A_203),A_203)
      | ~ v1_funct_1(C_205)
      | ~ m1_subset_1(B_204,A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_72,plain,
    ( r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_59,c_69])).

tff(c_184,plain,
    ( r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_136,c_72])).

tff(c_185,plain,(
    ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_188,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_185])).

tff(c_192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_28,c_188])).

tff(c_193,plain,
    ( ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_195,plain,(
    ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_198,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_195])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_28,c_198])).

tff(c_203,plain,(
    r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_20,plain,(
    ! [F_75,E_73,A_13,C_61,B_45,D_69] :
      ( r1_binop_1(A_13,C_61,E_73)
      | ~ r1_binop_1(k2_zfmisc_1(A_13,B_45),k1_domain_1(A_13,B_45,C_61,D_69),k6_filter_1(A_13,B_45,E_73,F_75))
      | ~ m1_subset_1(F_75,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_45,B_45),B_45)))
      | ~ v1_funct_2(F_75,k2_zfmisc_1(B_45,B_45),B_45)
      | ~ v1_funct_1(F_75)
      | ~ m1_subset_1(E_73,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_13,A_13),A_13)))
      | ~ v1_funct_2(E_73,k2_zfmisc_1(A_13,A_13),A_13)
      | ~ v1_funct_1(E_73)
      | ~ m1_subset_1(D_69,B_45)
      | ~ m1_subset_1(C_61,A_13)
      | v1_xboole_0(B_45)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_207,plain,
    ( r1_binop_1('#skF_1','#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_203,c_20])).

tff(c_213,plain,
    ( r1_binop_1('#skF_1','#skF_3','#skF_5')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_32,c_30,c_28,c_207])).

tff(c_215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_112,c_213])).

tff(c_216,plain,(
    ~ r2_binop_1('#skF_1','#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_218,plain,(
    ! [A_251,B_252,C_253,D_254] :
      ( v1_funct_1(k6_filter_1(A_251,B_252,C_253,D_254))
      | ~ m1_subset_1(D_254,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_252,B_252),B_252)))
      | ~ v1_funct_2(D_254,k2_zfmisc_1(B_252,B_252),B_252)
      | ~ v1_funct_1(D_254)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_251,A_251),A_251)))
      | ~ v1_funct_2(C_253,k2_zfmisc_1(A_251,A_251),A_251)
      | ~ v1_funct_1(C_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_220,plain,(
    ! [A_251,C_253] :
      ( v1_funct_1(k6_filter_1(A_251,'#skF_2',C_253,'#skF_6'))
      | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_251,A_251),A_251)))
      | ~ v1_funct_2(C_253,k2_zfmisc_1(A_251,A_251),A_251)
      | ~ v1_funct_1(C_253) ) ),
    inference(resolution,[status(thm)],[c_28,c_218])).

tff(c_229,plain,(
    ! [A_255,C_256] :
      ( v1_funct_1(k6_filter_1(A_255,'#skF_2',C_256,'#skF_6'))
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_255,A_255),A_255)))
      | ~ v1_funct_2(C_256,k2_zfmisc_1(A_255,A_255),A_255)
      | ~ v1_funct_1(C_256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_220])).

tff(c_235,plain,
    ( v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_229])).

tff(c_241,plain,(
    v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_235])).

tff(c_275,plain,
    ( r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_72])).

tff(c_276,plain,(
    ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_275])).

tff(c_279,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_276])).

tff(c_282,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_279])).

tff(c_284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_282])).

tff(c_286,plain,(
    m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_275])).

tff(c_285,plain,
    ( ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_275])).

tff(c_287,plain,(
    ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_290,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_287])).

tff(c_294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_28,c_290])).

tff(c_296,plain,(
    m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_331,plain,
    ( r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_241,c_296,c_68])).

tff(c_332,plain,(
    ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_335,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_332])).

tff(c_339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_28,c_335])).

tff(c_340,plain,(
    r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_26,plain,(
    ! [A_76,F_138,B_108,D_132,E_136,C_124] :
      ( r2_binop_1(A_76,C_124,E_136)
      | ~ r2_binop_1(k2_zfmisc_1(A_76,B_108),k1_domain_1(A_76,B_108,C_124,D_132),k6_filter_1(A_76,B_108,E_136,F_138))
      | ~ m1_subset_1(F_138,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_108,B_108),B_108)))
      | ~ v1_funct_2(F_138,k2_zfmisc_1(B_108,B_108),B_108)
      | ~ v1_funct_1(F_138)
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_76,A_76),A_76)))
      | ~ v1_funct_2(E_136,k2_zfmisc_1(A_76,A_76),A_76)
      | ~ v1_funct_1(E_136)
      | ~ m1_subset_1(D_132,B_108)
      | ~ m1_subset_1(C_124,A_76)
      | v1_xboole_0(B_108)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_347,plain,
    ( r2_binop_1('#skF_1','#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_340,c_26])).

tff(c_354,plain,
    ( r2_binop_1('#skF_1','#skF_3','#skF_5')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_32,c_30,c_28,c_347])).

tff(c_356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_216,c_354])).

tff(c_357,plain,(
    ~ r3_binop_1('#skF_2','#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_395,plain,
    ( ~ r2_binop_1('#skF_2','#skF_4','#skF_6')
    | ~ r1_binop_1('#skF_2','#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_388,c_357])).

tff(c_404,plain,
    ( ~ r2_binop_1('#skF_2','#skF_4','#skF_6')
    | ~ r1_binop_1('#skF_2','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_395])).

tff(c_405,plain,(
    ~ r1_binop_1('#skF_2','#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_404])).

tff(c_417,plain,(
    ! [A_302,B_303,C_304,D_305] :
      ( v1_funct_1(k6_filter_1(A_302,B_303,C_304,D_305))
      | ~ m1_subset_1(D_305,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_303,B_303),B_303)))
      | ~ v1_funct_2(D_305,k2_zfmisc_1(B_303,B_303),B_303)
      | ~ v1_funct_1(D_305)
      | ~ m1_subset_1(C_304,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_302,A_302),A_302)))
      | ~ v1_funct_2(C_304,k2_zfmisc_1(A_302,A_302),A_302)
      | ~ v1_funct_1(C_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_419,plain,(
    ! [A_302,C_304] :
      ( v1_funct_1(k6_filter_1(A_302,'#skF_2',C_304,'#skF_6'))
      | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_304,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_302,A_302),A_302)))
      | ~ v1_funct_2(C_304,k2_zfmisc_1(A_302,A_302),A_302)
      | ~ v1_funct_1(C_304) ) ),
    inference(resolution,[status(thm)],[c_28,c_417])).

tff(c_428,plain,(
    ! [A_306,C_307] :
      ( v1_funct_1(k6_filter_1(A_306,'#skF_2',C_307,'#skF_6'))
      | ~ m1_subset_1(C_307,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_306,A_306),A_306)))
      | ~ v1_funct_2(C_307,k2_zfmisc_1(A_306,A_306),A_306)
      | ~ v1_funct_1(C_307) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_419])).

tff(c_434,plain,
    ( v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_428])).

tff(c_440,plain,(
    v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_434])).

tff(c_368,plain,(
    ! [A_294,B_295,C_296] :
      ( r1_binop_1(A_294,B_295,C_296)
      | ~ r3_binop_1(A_294,B_295,C_296)
      | ~ m1_subset_1(C_296,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_294,A_294),A_294)))
      | ~ v1_funct_2(C_296,k2_zfmisc_1(A_294,A_294),A_294)
      | ~ v1_funct_1(C_296)
      | ~ m1_subset_1(B_295,A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_376,plain,
    ( r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_59,c_368])).

tff(c_475,plain,
    ( r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_376])).

tff(c_476,plain,(
    ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_475])).

tff(c_479,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_476])).

tff(c_482,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_479])).

tff(c_484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_482])).

tff(c_486,plain,(
    m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_475])).

tff(c_359,plain,(
    ! [A_291,B_292,C_293] :
      ( r2_binop_1(A_291,B_292,C_293)
      | ~ r3_binop_1(A_291,B_292,C_293)
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_291,A_291),A_291)))
      | ~ v1_funct_2(C_293,k2_zfmisc_1(A_291,A_291),A_291)
      | ~ v1_funct_1(C_293)
      | ~ m1_subset_1(B_292,A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_367,plain,
    ( r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_59,c_359])).

tff(c_488,plain,
    ( r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_440,c_367])).

tff(c_489,plain,(
    ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_488])).

tff(c_492,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_489])).

tff(c_496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_28,c_492])).

tff(c_497,plain,
    ( ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_488])).

tff(c_499,plain,(
    ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_497])).

tff(c_502,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_499])).

tff(c_506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_28,c_502])).

tff(c_508,plain,(
    m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_497])).

tff(c_498,plain,(
    v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_488])).

tff(c_485,plain,
    ( ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_475])).

tff(c_610,plain,(
    r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_498,c_485])).

tff(c_18,plain,(
    ! [F_75,E_73,A_13,C_61,B_45,D_69] :
      ( r1_binop_1(B_45,D_69,F_75)
      | ~ r1_binop_1(k2_zfmisc_1(A_13,B_45),k1_domain_1(A_13,B_45,C_61,D_69),k6_filter_1(A_13,B_45,E_73,F_75))
      | ~ m1_subset_1(F_75,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_45,B_45),B_45)))
      | ~ v1_funct_2(F_75,k2_zfmisc_1(B_45,B_45),B_45)
      | ~ v1_funct_1(F_75)
      | ~ m1_subset_1(E_73,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_13,A_13),A_13)))
      | ~ v1_funct_2(E_73,k2_zfmisc_1(A_13,A_13),A_13)
      | ~ v1_funct_1(E_73)
      | ~ m1_subset_1(D_69,B_45)
      | ~ m1_subset_1(C_61,A_13)
      | v1_xboole_0(B_45)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_616,plain,
    ( r1_binop_1('#skF_2','#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_610,c_18])).

tff(c_623,plain,
    ( r1_binop_1('#skF_2','#skF_4','#skF_6')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_32,c_30,c_28,c_616])).

tff(c_625,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_405,c_623])).

tff(c_626,plain,(
    ~ r2_binop_1('#skF_2','#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_404])).

tff(c_639,plain,(
    ! [A_362,B_363,C_364,D_365] :
      ( v1_funct_1(k6_filter_1(A_362,B_363,C_364,D_365))
      | ~ m1_subset_1(D_365,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_363,B_363),B_363)))
      | ~ v1_funct_2(D_365,k2_zfmisc_1(B_363,B_363),B_363)
      | ~ v1_funct_1(D_365)
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_362,A_362),A_362)))
      | ~ v1_funct_2(C_364,k2_zfmisc_1(A_362,A_362),A_362)
      | ~ v1_funct_1(C_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_641,plain,(
    ! [A_362,C_364] :
      ( v1_funct_1(k6_filter_1(A_362,'#skF_2',C_364,'#skF_6'))
      | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_362,A_362),A_362)))
      | ~ v1_funct_2(C_364,k2_zfmisc_1(A_362,A_362),A_362)
      | ~ v1_funct_1(C_364) ) ),
    inference(resolution,[status(thm)],[c_28,c_639])).

tff(c_650,plain,(
    ! [A_366,C_367] :
      ( v1_funct_1(k6_filter_1(A_366,'#skF_2',C_367,'#skF_6'))
      | ~ m1_subset_1(C_367,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_366,A_366),A_366)))
      | ~ v1_funct_2(C_367,k2_zfmisc_1(A_366,A_366),A_366)
      | ~ v1_funct_1(C_367) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_641])).

tff(c_656,plain,
    ( v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_650])).

tff(c_662,plain,(
    v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_656])).

tff(c_706,plain,
    ( r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_367])).

tff(c_707,plain,(
    ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_706])).

tff(c_710,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_707])).

tff(c_713,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_710])).

tff(c_715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_713])).

tff(c_717,plain,(
    m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_706])).

tff(c_719,plain,
    ( r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_662,c_376])).

tff(c_720,plain,(
    ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_719])).

tff(c_723,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_720])).

tff(c_727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_28,c_723])).

tff(c_728,plain,
    ( ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_719])).

tff(c_730,plain,(
    ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_728])).

tff(c_733,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_730])).

tff(c_737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_28,c_733])).

tff(c_739,plain,(
    m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_728])).

tff(c_729,plain,(
    v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_719])).

tff(c_716,plain,
    ( ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_706])).

tff(c_840,plain,(
    r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_739,c_729,c_716])).

tff(c_24,plain,(
    ! [A_76,F_138,B_108,D_132,E_136,C_124] :
      ( r2_binop_1(B_108,D_132,F_138)
      | ~ r2_binop_1(k2_zfmisc_1(A_76,B_108),k1_domain_1(A_76,B_108,C_124,D_132),k6_filter_1(A_76,B_108,E_136,F_138))
      | ~ m1_subset_1(F_138,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_108,B_108),B_108)))
      | ~ v1_funct_2(F_138,k2_zfmisc_1(B_108,B_108),B_108)
      | ~ v1_funct_1(F_138)
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_76,A_76),A_76)))
      | ~ v1_funct_2(E_136,k2_zfmisc_1(A_76,A_76),A_76)
      | ~ v1_funct_1(E_136)
      | ~ m1_subset_1(D_132,B_108)
      | ~ m1_subset_1(C_124,A_76)
      | v1_xboole_0(B_108)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_846,plain,
    ( r2_binop_1('#skF_2','#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_840,c_24])).

tff(c_853,plain,
    ( r2_binop_1('#skF_2','#skF_4','#skF_6')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_32,c_30,c_28,c_846])).

tff(c_855,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_626,c_853])).

tff(c_857,plain,(
    ~ r3_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_58,plain,
    ( r3_binop_1('#skF_1','#skF_3','#skF_5')
    | r3_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_858,plain,(
    r3_binop_1('#skF_1','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_857,c_58])).

tff(c_862,plain,(
    ! [A_431,B_432,C_433] :
      ( r1_binop_1(A_431,B_432,C_433)
      | ~ r3_binop_1(A_431,B_432,C_433)
      | ~ m1_subset_1(C_433,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_431,A_431),A_431)))
      | ~ v1_funct_2(C_433,k2_zfmisc_1(A_431,A_431),A_431)
      | ~ v1_funct_1(C_433)
      | ~ m1_subset_1(B_432,A_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_864,plain,
    ( r1_binop_1('#skF_1','#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_858,c_862])).

tff(c_869,plain,(
    r1_binop_1('#skF_1','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_36,c_34,c_864])).

tff(c_856,plain,(
    r3_binop_1('#skF_2','#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_866,plain,
    ( r1_binop_1('#skF_2','#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_856,c_862])).

tff(c_872,plain,(
    r1_binop_1('#skF_2','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_30,c_28,c_866])).

tff(c_16,plain,(
    ! [F_75,E_73,A_13,C_61,B_45,D_69] :
      ( r1_binop_1(k2_zfmisc_1(A_13,B_45),k1_domain_1(A_13,B_45,C_61,D_69),k6_filter_1(A_13,B_45,E_73,F_75))
      | ~ r1_binop_1(B_45,D_69,F_75)
      | ~ r1_binop_1(A_13,C_61,E_73)
      | ~ m1_subset_1(F_75,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_45,B_45),B_45)))
      | ~ v1_funct_2(F_75,k2_zfmisc_1(B_45,B_45),B_45)
      | ~ v1_funct_1(F_75)
      | ~ m1_subset_1(E_73,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_13,A_13),A_13)))
      | ~ v1_funct_2(E_73,k2_zfmisc_1(A_13,A_13),A_13)
      | ~ v1_funct_1(E_73)
      | ~ m1_subset_1(D_69,B_45)
      | ~ m1_subset_1(C_61,A_13)
      | v1_xboole_0(B_45)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_873,plain,(
    ! [A_434,B_435,C_436] :
      ( r2_binop_1(A_434,B_435,C_436)
      | ~ r3_binop_1(A_434,B_435,C_436)
      | ~ m1_subset_1(C_436,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_434,A_434),A_434)))
      | ~ v1_funct_2(C_436,k2_zfmisc_1(A_434,A_434),A_434)
      | ~ v1_funct_1(C_436)
      | ~ m1_subset_1(B_435,A_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_875,plain,
    ( r2_binop_1('#skF_1','#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_858,c_873])).

tff(c_880,plain,(
    r2_binop_1('#skF_1','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_36,c_34,c_875])).

tff(c_877,plain,
    ( r2_binop_1('#skF_2','#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_856,c_873])).

tff(c_883,plain,(
    r2_binop_1('#skF_2','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_30,c_28,c_877])).

tff(c_22,plain,(
    ! [A_76,F_138,B_108,D_132,E_136,C_124] :
      ( r2_binop_1(k2_zfmisc_1(A_76,B_108),k1_domain_1(A_76,B_108,C_124,D_132),k6_filter_1(A_76,B_108,E_136,F_138))
      | ~ r2_binop_1(B_108,D_132,F_138)
      | ~ r2_binop_1(A_76,C_124,E_136)
      | ~ m1_subset_1(F_138,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_108,B_108),B_108)))
      | ~ v1_funct_2(F_138,k2_zfmisc_1(B_108,B_108),B_108)
      | ~ v1_funct_1(F_138)
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_76,A_76),A_76)))
      | ~ v1_funct_2(E_136,k2_zfmisc_1(A_76,A_76),A_76)
      | ~ v1_funct_1(E_136)
      | ~ m1_subset_1(D_132,B_108)
      | ~ m1_subset_1(C_124,A_76)
      | v1_xboole_0(B_108)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_917,plain,(
    ! [A_442,B_443,C_444,D_445] :
      ( v1_funct_1(k6_filter_1(A_442,B_443,C_444,D_445))
      | ~ m1_subset_1(D_445,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_443,B_443),B_443)))
      | ~ v1_funct_2(D_445,k2_zfmisc_1(B_443,B_443),B_443)
      | ~ v1_funct_1(D_445)
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_442,A_442),A_442)))
      | ~ v1_funct_2(C_444,k2_zfmisc_1(A_442,A_442),A_442)
      | ~ v1_funct_1(C_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_919,plain,(
    ! [A_442,C_444] :
      ( v1_funct_1(k6_filter_1(A_442,'#skF_2',C_444,'#skF_6'))
      | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_442,A_442),A_442)))
      | ~ v1_funct_2(C_444,k2_zfmisc_1(A_442,A_442),A_442)
      | ~ v1_funct_1(C_444) ) ),
    inference(resolution,[status(thm)],[c_28,c_917])).

tff(c_928,plain,(
    ! [A_446,C_447] :
      ( v1_funct_1(k6_filter_1(A_446,'#skF_2',C_447,'#skF_6'))
      | ~ m1_subset_1(C_447,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_446,A_446),A_446)))
      | ~ v1_funct_2(C_447,k2_zfmisc_1(A_446,A_446),A_446)
      | ~ v1_funct_1(C_447) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_919])).

tff(c_934,plain,
    ( v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_928])).

tff(c_940,plain,(
    v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_934])).

tff(c_955,plain,(
    ! [A_454,B_455,C_456,D_457] :
      ( m1_subset_1(k6_filter_1(A_454,B_455,C_456,D_457),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_454,B_455),k2_zfmisc_1(A_454,B_455)),k2_zfmisc_1(A_454,B_455))))
      | ~ m1_subset_1(D_457,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_455,B_455),B_455)))
      | ~ v1_funct_2(D_457,k2_zfmisc_1(B_455,B_455),B_455)
      | ~ v1_funct_1(D_457)
      | ~ m1_subset_1(C_456,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_454,A_454),A_454)))
      | ~ v1_funct_2(C_456,k2_zfmisc_1(A_454,A_454),A_454)
      | ~ v1_funct_1(C_456) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [A_1,B_2,C_4] :
      ( r3_binop_1(A_1,B_2,C_4)
      | ~ r2_binop_1(A_1,B_2,C_4)
      | ~ r1_binop_1(A_1,B_2,C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1,A_1),A_1)))
      | ~ v1_funct_2(C_4,k2_zfmisc_1(A_1,A_1),A_1)
      | ~ v1_funct_1(C_4)
      | ~ m1_subset_1(B_2,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1130,plain,(
    ! [B_536,A_538,D_535,C_537,B_534] :
      ( r3_binop_1(k2_zfmisc_1(A_538,B_534),B_536,k6_filter_1(A_538,B_534,C_537,D_535))
      | ~ r2_binop_1(k2_zfmisc_1(A_538,B_534),B_536,k6_filter_1(A_538,B_534,C_537,D_535))
      | ~ r1_binop_1(k2_zfmisc_1(A_538,B_534),B_536,k6_filter_1(A_538,B_534,C_537,D_535))
      | ~ v1_funct_2(k6_filter_1(A_538,B_534,C_537,D_535),k2_zfmisc_1(k2_zfmisc_1(A_538,B_534),k2_zfmisc_1(A_538,B_534)),k2_zfmisc_1(A_538,B_534))
      | ~ v1_funct_1(k6_filter_1(A_538,B_534,C_537,D_535))
      | ~ m1_subset_1(B_536,k2_zfmisc_1(A_538,B_534))
      | ~ m1_subset_1(D_535,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_534,B_534),B_534)))
      | ~ v1_funct_2(D_535,k2_zfmisc_1(B_534,B_534),B_534)
      | ~ v1_funct_1(D_535)
      | ~ m1_subset_1(C_537,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_538,A_538),A_538)))
      | ~ v1_funct_2(C_537,k2_zfmisc_1(A_538,A_538),A_538)
      | ~ v1_funct_1(C_537) ) ),
    inference(resolution,[status(thm)],[c_955,c_2])).

tff(c_1199,plain,(
    ! [C_551,B_549,D_552,B_550,A_553] :
      ( r3_binop_1(k2_zfmisc_1(A_553,B_550),B_549,k6_filter_1(A_553,B_550,C_551,D_552))
      | ~ r2_binop_1(k2_zfmisc_1(A_553,B_550),B_549,k6_filter_1(A_553,B_550,C_551,D_552))
      | ~ r1_binop_1(k2_zfmisc_1(A_553,B_550),B_549,k6_filter_1(A_553,B_550,C_551,D_552))
      | ~ v1_funct_1(k6_filter_1(A_553,B_550,C_551,D_552))
      | ~ m1_subset_1(B_549,k2_zfmisc_1(A_553,B_550))
      | ~ m1_subset_1(D_552,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_550,B_550),B_550)))
      | ~ v1_funct_2(D_552,k2_zfmisc_1(B_550,B_550),B_550)
      | ~ v1_funct_1(D_552)
      | ~ m1_subset_1(C_551,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_553,A_553),A_553)))
      | ~ v1_funct_2(C_551,k2_zfmisc_1(A_553,A_553),A_553)
      | ~ v1_funct_1(C_551) ) ),
    inference(resolution,[status(thm)],[c_12,c_1130])).

tff(c_1203,plain,(
    ! [A_553,B_549,C_551] :
      ( r3_binop_1(k2_zfmisc_1(A_553,'#skF_2'),B_549,k6_filter_1(A_553,'#skF_2',C_551,'#skF_6'))
      | ~ r2_binop_1(k2_zfmisc_1(A_553,'#skF_2'),B_549,k6_filter_1(A_553,'#skF_2',C_551,'#skF_6'))
      | ~ r1_binop_1(k2_zfmisc_1(A_553,'#skF_2'),B_549,k6_filter_1(A_553,'#skF_2',C_551,'#skF_6'))
      | ~ v1_funct_1(k6_filter_1(A_553,'#skF_2',C_551,'#skF_6'))
      | ~ m1_subset_1(B_549,k2_zfmisc_1(A_553,'#skF_2'))
      | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_551,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_553,A_553),A_553)))
      | ~ v1_funct_2(C_551,k2_zfmisc_1(A_553,A_553),A_553)
      | ~ v1_funct_1(C_551) ) ),
    inference(resolution,[status(thm)],[c_28,c_1199])).

tff(c_1266,plain,(
    ! [A_561,B_562,C_563] :
      ( r3_binop_1(k2_zfmisc_1(A_561,'#skF_2'),B_562,k6_filter_1(A_561,'#skF_2',C_563,'#skF_6'))
      | ~ r2_binop_1(k2_zfmisc_1(A_561,'#skF_2'),B_562,k6_filter_1(A_561,'#skF_2',C_563,'#skF_6'))
      | ~ r1_binop_1(k2_zfmisc_1(A_561,'#skF_2'),B_562,k6_filter_1(A_561,'#skF_2',C_563,'#skF_6'))
      | ~ v1_funct_1(k6_filter_1(A_561,'#skF_2',C_563,'#skF_6'))
      | ~ m1_subset_1(B_562,k2_zfmisc_1(A_561,'#skF_2'))
      | ~ m1_subset_1(C_563,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_561,A_561),A_561)))
      | ~ v1_funct_2(C_563,k2_zfmisc_1(A_561,A_561),A_561)
      | ~ v1_funct_1(C_563) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1203])).

tff(c_1272,plain,(
    ! [B_562] :
      ( r3_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),B_562,k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
      | ~ r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),B_562,k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
      | ~ r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),B_562,k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
      | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1(B_562,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_1266])).

tff(c_1295,plain,(
    ! [B_573] :
      ( r3_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),B_573,k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
      | ~ r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),B_573,k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
      | ~ r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),B_573,k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
      | ~ m1_subset_1(B_573,k2_zfmisc_1('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_940,c_1272])).

tff(c_1309,plain,
    ( ~ r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1295,c_857])).

tff(c_1310,plain,(
    ~ m1_subset_1(k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1309])).

tff(c_1313,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_1310])).

tff(c_1316,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1313])).

tff(c_1318,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_1316])).

tff(c_1319,plain,
    ( ~ r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6'))
    | ~ r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1309])).

tff(c_1321,plain,(
    ~ r2_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1319])).

tff(c_1324,plain,
    ( ~ r2_binop_1('#skF_2','#skF_4','#skF_6')
    | ~ r2_binop_1('#skF_1','#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1321])).

tff(c_1327,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_32,c_30,c_28,c_880,c_883,c_1324])).

tff(c_1329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_1327])).

tff(c_1330,plain,(
    ~ r1_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k1_domain_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_filter_1('#skF_1','#skF_2','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1319])).

tff(c_1334,plain,
    ( ~ r1_binop_1('#skF_2','#skF_4','#skF_6')
    | ~ r1_binop_1('#skF_1','#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_1330])).

tff(c_1337,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_32,c_30,c_28,c_869,c_872,c_1334])).

tff(c_1339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_1337])).

%------------------------------------------------------------------------------
