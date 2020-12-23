%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:37 EST 2020

% Result     : Theorem 10.14s
% Output     : CNFRefutation 10.39s
% Verified   : 
% Statistics : Number of formulae       :  239 (2951 expanded)
%              Number of leaves         :   24 (1115 expanded)
%              Depth                    :   17
%              Number of atoms          :  955 (22278 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r6_binop_1 > r5_binop_1 > r4_binop_1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k6_filter_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r6_binop_1,type,(
    r6_binop_1: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k6_filter_1,type,(
    k6_filter_1: ( $i * $i * $i * $i ) > $i )).

tff(r4_binop_1,type,(
    r4_binop_1: ( $i * $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r5_binop_1,type,(
    r5_binop_1: ( $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_186,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,k2_zfmisc_1(A,A),A)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,k2_zfmisc_1(A,A),A)
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,k2_zfmisc_1(B,B),B)
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,k2_zfmisc_1(B,B),B)
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
                           => ( ( r6_binop_1(A,C,D)
                                & r6_binop_1(B,E,F) )
                            <=> r6_binop_1(k2_zfmisc_1(A,B),k6_filter_1(A,B,C,E),k6_filter_1(A,B,D,F)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_filter_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,k2_zfmisc_1(A,A),A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
     => ! [C] :
          ( ( v1_funct_1(C)
            & v1_funct_2(C,k2_zfmisc_1(A,A),A)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
         => ( r6_binop_1(A,B,C)
          <=> ( r4_binop_1(A,B,C)
              & r5_binop_1(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_binop_1)).

tff(f_62,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_filter_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,k2_zfmisc_1(A,A),A)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,k2_zfmisc_1(A,A),A)
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,k2_zfmisc_1(B,B),B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,k2_zfmisc_1(B,B),B)
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
                         => ( ( r4_binop_1(A,C,D)
                              & r4_binop_1(B,E,F) )
                          <=> r4_binop_1(k2_zfmisc_1(A,B),k6_filter_1(A,B,C,E),k6_filter_1(A,B,D,F)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_filter_1)).

tff(f_144,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,k2_zfmisc_1(A,A),A)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,k2_zfmisc_1(A,A),A)
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,k2_zfmisc_1(B,B),B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,k2_zfmisc_1(B,B),B)
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
                         => ( ( r5_binop_1(A,C,D)
                              & r5_binop_1(B,E,F) )
                          <=> r5_binop_1(k2_zfmisc_1(A,B),k6_filter_1(A,B,C,E),k6_filter_1(A,B,D,F)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_filter_1)).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_46,plain,(
    v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_40,plain,(
    v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_34,plain,(
    v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_30,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_28,plain,(
    v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_62,plain,
    ( r6_binop_1('#skF_2','#skF_5','#skF_6')
    | r6_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_65,plain,(
    r6_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_54,plain,
    ( ~ r6_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ r6_binop_1('#skF_2','#skF_5','#skF_6')
    | ~ r6_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_68,plain,
    ( ~ r6_binop_1('#skF_2','#skF_5','#skF_6')
    | ~ r6_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_54])).

tff(c_69,plain,(
    ~ r6_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_199,plain,(
    ! [A_210,B_211,C_212] :
      ( r6_binop_1(A_210,B_211,C_212)
      | ~ r5_binop_1(A_210,B_211,C_212)
      | ~ r4_binop_1(A_210,B_211,C_212)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_210,A_210),A_210)))
      | ~ v1_funct_2(C_212,k2_zfmisc_1(A_210,A_210),A_210)
      | ~ v1_funct_1(C_212)
      | ~ m1_subset_1(B_211,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_210,A_210),A_210)))
      | ~ v1_funct_2(B_211,k2_zfmisc_1(A_210,A_210),A_210)
      | ~ v1_funct_1(B_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_205,plain,(
    ! [B_211] :
      ( r6_binop_1('#skF_1',B_211,'#skF_4')
      | ~ r5_binop_1('#skF_1',B_211,'#skF_4')
      | ~ r4_binop_1('#skF_1',B_211,'#skF_4')
      | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(B_211,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(B_211,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(B_211) ) ),
    inference(resolution,[status(thm)],[c_38,c_199])).

tff(c_236,plain,(
    ! [B_218] :
      ( r6_binop_1('#skF_1',B_218,'#skF_4')
      | ~ r5_binop_1('#skF_1',B_218,'#skF_4')
      | ~ r4_binop_1('#skF_1',B_218,'#skF_4')
      | ~ m1_subset_1(B_218,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(B_218,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(B_218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_205])).

tff(c_239,plain,
    ( r6_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ r5_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ r4_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_236])).

tff(c_245,plain,
    ( r6_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ r5_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ r4_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_239])).

tff(c_246,plain,
    ( ~ r5_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ r4_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_245])).

tff(c_250,plain,(
    ~ r4_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7,D_8] :
      ( m1_subset_1(k6_filter_1(A_5,B_6,C_7,D_8),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_5,B_6),k2_zfmisc_1(A_5,B_6)),k2_zfmisc_1(A_5,B_6))))
      | ~ m1_subset_1(D_8,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_6,B_6),B_6)))
      | ~ v1_funct_2(D_8,k2_zfmisc_1(B_6,B_6),B_6)
      | ~ v1_funct_1(D_8)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_5,A_5),A_5)))
      | ~ v1_funct_2(C_7,k2_zfmisc_1(A_5,A_5),A_5)
      | ~ v1_funct_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_70,plain,(
    ! [A_192,B_193,C_194,D_195] :
      ( v1_funct_1(k6_filter_1(A_192,B_193,C_194,D_195))
      | ~ m1_subset_1(D_195,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_193,B_193),B_193)))
      | ~ v1_funct_2(D_195,k2_zfmisc_1(B_193,B_193),B_193)
      | ~ v1_funct_1(D_195)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_192,A_192),A_192)))
      | ~ v1_funct_2(C_194,k2_zfmisc_1(A_192,A_192),A_192)
      | ~ v1_funct_1(C_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_78,plain,(
    ! [A_192,C_194] :
      ( v1_funct_1(k6_filter_1(A_192,'#skF_2',C_194,'#skF_5'))
      | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_192,A_192),A_192)))
      | ~ v1_funct_2(C_194,k2_zfmisc_1(A_192,A_192),A_192)
      | ~ v1_funct_1(C_194) ) ),
    inference(resolution,[status(thm)],[c_32,c_70])).

tff(c_174,plain,(
    ! [A_208,C_209] :
      ( v1_funct_1(k6_filter_1(A_208,'#skF_2',C_209,'#skF_5'))
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_208,A_208),A_208)))
      | ~ v1_funct_2(C_209,k2_zfmisc_1(A_208,A_208),A_208)
      | ~ v1_funct_1(C_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_78])).

tff(c_177,plain,
    ( v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_174])).

tff(c_189,plain,(
    v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_177])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7,D_8] :
      ( v1_funct_2(k6_filter_1(A_5,B_6,C_7,D_8),k2_zfmisc_1(k2_zfmisc_1(A_5,B_6),k2_zfmisc_1(A_5,B_6)),k2_zfmisc_1(A_5,B_6))
      | ~ m1_subset_1(D_8,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_6,B_6),B_6)))
      | ~ v1_funct_2(D_8,k2_zfmisc_1(B_6,B_6),B_6)
      | ~ v1_funct_1(D_8)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_5,A_5),A_5)))
      | ~ v1_funct_2(C_7,k2_zfmisc_1(A_5,A_5),A_5)
      | ~ v1_funct_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_74,plain,(
    ! [A_192,C_194] :
      ( v1_funct_1(k6_filter_1(A_192,'#skF_2',C_194,'#skF_6'))
      | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_192,A_192),A_192)))
      | ~ v1_funct_2(C_194,k2_zfmisc_1(A_192,A_192),A_192)
      | ~ v1_funct_1(C_194) ) ),
    inference(resolution,[status(thm)],[c_26,c_70])).

tff(c_145,plain,(
    ! [A_203,C_204] :
      ( v1_funct_1(k6_filter_1(A_203,'#skF_2',C_204,'#skF_6'))
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_203,A_203),A_203)))
      | ~ v1_funct_2(C_204,k2_zfmisc_1(A_203,A_203),A_203)
      | ~ v1_funct_1(C_204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_74])).

tff(c_154,plain,
    ( v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_145])).

tff(c_166,plain,(
    v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_154])).

tff(c_170,plain,(
    ! [A_205,B_206,C_207] :
      ( r4_binop_1(A_205,B_206,C_207)
      | ~ r6_binop_1(A_205,B_206,C_207)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_205,A_205),A_205)))
      | ~ v1_funct_2(C_207,k2_zfmisc_1(A_205,A_205),A_205)
      | ~ v1_funct_1(C_207)
      | ~ m1_subset_1(B_206,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_205,A_205),A_205)))
      | ~ v1_funct_2(B_206,k2_zfmisc_1(A_205,A_205),A_205)
      | ~ v1_funct_1(B_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_173,plain,
    ( r4_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_65,c_170])).

tff(c_767,plain,
    ( r4_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_166,c_173])).

tff(c_768,plain,(
    ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_767])).

tff(c_774,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_768])).

tff(c_778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_36,c_34,c_32,c_774])).

tff(c_780,plain,(
    v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_767])).

tff(c_116,plain,(
    ! [A_198,B_199,C_200] :
      ( r5_binop_1(A_198,B_199,C_200)
      | ~ r6_binop_1(A_198,B_199,C_200)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_198,A_198),A_198)))
      | ~ v1_funct_2(C_200,k2_zfmisc_1(A_198,A_198),A_198)
      | ~ v1_funct_1(C_200)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_198,A_198),A_198)))
      | ~ v1_funct_2(B_199,k2_zfmisc_1(A_198,A_198),A_198)
      | ~ v1_funct_1(B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_119,plain,
    ( r5_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_65,c_116])).

tff(c_787,plain,
    ( r5_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_780,c_166,c_119])).

tff(c_788,plain,(
    ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_787])).

tff(c_791,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_788])).

tff(c_795,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_36,c_34,c_32,c_791])).

tff(c_796,plain,
    ( ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | r5_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_787])).

tff(c_983,plain,(
    ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_796])).

tff(c_986,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_983])).

tff(c_990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_30,c_28,c_26,c_986])).

tff(c_992,plain,(
    m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_796])).

tff(c_991,plain,
    ( ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | r5_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_796])).

tff(c_1139,plain,(
    ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_991])).

tff(c_1142,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_1139])).

tff(c_1146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_30,c_28,c_26,c_1142])).

tff(c_1148,plain,(
    v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_991])).

tff(c_797,plain,(
    m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_787])).

tff(c_779,plain,
    ( ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | r4_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_767])).

tff(c_1314,plain,(
    r4_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_992,c_1148,c_797,c_779])).

tff(c_18,plain,(
    ! [F_71,C_57,E_69,D_65,B_41,A_9] :
      ( r4_binop_1(A_9,C_57,D_65)
      | ~ r4_binop_1(k2_zfmisc_1(A_9,B_41),k6_filter_1(A_9,B_41,C_57,E_69),k6_filter_1(A_9,B_41,D_65,F_71))
      | ~ m1_subset_1(F_71,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_41,B_41),B_41)))
      | ~ v1_funct_2(F_71,k2_zfmisc_1(B_41,B_41),B_41)
      | ~ v1_funct_1(F_71)
      | ~ m1_subset_1(E_69,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_41,B_41),B_41)))
      | ~ v1_funct_2(E_69,k2_zfmisc_1(B_41,B_41),B_41)
      | ~ v1_funct_1(E_69)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9,A_9),A_9)))
      | ~ v1_funct_2(D_65,k2_zfmisc_1(A_9,A_9),A_9)
      | ~ v1_funct_1(D_65)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9,A_9),A_9)))
      | ~ v1_funct_2(C_57,k2_zfmisc_1(A_9,A_9),A_9)
      | ~ v1_funct_1(C_57)
      | v1_xboole_0(B_41)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1317,plain,
    ( r4_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1314,c_18])).

tff(c_1323,plain,
    ( r4_binop_1('#skF_1','#skF_3','#skF_4')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_38,c_36,c_34,c_32,c_30,c_28,c_26,c_1317])).

tff(c_1325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_250,c_1323])).

tff(c_1326,plain,(
    ~ r5_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_3921,plain,
    ( r4_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_166,c_173])).

tff(c_3922,plain,(
    ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3921])).

tff(c_3925,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_3922])).

tff(c_3929,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_36,c_34,c_32,c_3925])).

tff(c_3931,plain,(
    v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_3921])).

tff(c_3967,plain,
    ( r5_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_3931,c_166,c_119])).

tff(c_3968,plain,(
    ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_3967])).

tff(c_3971,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_3968])).

tff(c_3975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_36,c_34,c_32,c_3971])).

tff(c_3976,plain,
    ( ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | r5_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_3967])).

tff(c_4125,plain,(
    ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_3976])).

tff(c_4128,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_4125])).

tff(c_4132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_30,c_28,c_26,c_4128])).

tff(c_4134,plain,(
    m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_3976])).

tff(c_84,plain,(
    ! [A_192,C_194] :
      ( v1_funct_1(k6_filter_1(A_192,'#skF_2',C_194,'#skF_6'))
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_192,A_192),A_192)))
      | ~ v1_funct_2(C_194,k2_zfmisc_1(A_192,A_192),A_192)
      | ~ v1_funct_1(C_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_74])).

tff(c_4187,plain,
    ( v1_funct_1(k6_filter_1(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_2',k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),'#skF_6'))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_4134,c_84])).

tff(c_4252,plain,
    ( v1_funct_1(k6_filter_1(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_2',k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),'#skF_6'))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_4187])).

tff(c_4262,plain,(
    ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4252])).

tff(c_4274,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_4262])).

tff(c_4278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_30,c_28,c_26,c_4274])).

tff(c_4280,plain,(
    v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_4252])).

tff(c_4133,plain,
    ( ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | r5_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_3976])).

tff(c_4339,plain,(
    r5_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4280,c_4133])).

tff(c_24,plain,(
    ! [B_104,E_132,F_134,A_72,C_120,D_128] :
      ( r5_binop_1(A_72,C_120,D_128)
      | ~ r5_binop_1(k2_zfmisc_1(A_72,B_104),k6_filter_1(A_72,B_104,C_120,E_132),k6_filter_1(A_72,B_104,D_128,F_134))
      | ~ m1_subset_1(F_134,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_104,B_104),B_104)))
      | ~ v1_funct_2(F_134,k2_zfmisc_1(B_104,B_104),B_104)
      | ~ v1_funct_1(F_134)
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_104,B_104),B_104)))
      | ~ v1_funct_2(E_132,k2_zfmisc_1(B_104,B_104),B_104)
      | ~ v1_funct_1(E_132)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_72,A_72),A_72)))
      | ~ v1_funct_2(D_128,k2_zfmisc_1(A_72,A_72),A_72)
      | ~ v1_funct_1(D_128)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_72,A_72),A_72)))
      | ~ v1_funct_2(C_120,k2_zfmisc_1(A_72,A_72),A_72)
      | ~ v1_funct_1(C_120)
      | v1_xboole_0(B_104)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_4345,plain,
    ( r5_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4339,c_24])).

tff(c_4352,plain,
    ( r5_binop_1('#skF_1','#skF_3','#skF_4')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_38,c_36,c_34,c_32,c_30,c_28,c_26,c_4345])).

tff(c_4354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_1326,c_4352])).

tff(c_4355,plain,(
    ~ r6_binop_1('#skF_2','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_4498,plain,(
    ! [A_716,B_717,C_718] :
      ( r6_binop_1(A_716,B_717,C_718)
      | ~ r5_binop_1(A_716,B_717,C_718)
      | ~ r4_binop_1(A_716,B_717,C_718)
      | ~ m1_subset_1(C_718,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_716,A_716),A_716)))
      | ~ v1_funct_2(C_718,k2_zfmisc_1(A_716,A_716),A_716)
      | ~ v1_funct_1(C_718)
      | ~ m1_subset_1(B_717,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_716,A_716),A_716)))
      | ~ v1_funct_2(B_717,k2_zfmisc_1(A_716,A_716),A_716)
      | ~ v1_funct_1(B_717) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4502,plain,(
    ! [B_717] :
      ( r6_binop_1('#skF_2',B_717,'#skF_6')
      | ~ r5_binop_1('#skF_2',B_717,'#skF_6')
      | ~ r4_binop_1('#skF_2',B_717,'#skF_6')
      | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(B_717,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
      | ~ v1_funct_2(B_717,k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1(B_717) ) ),
    inference(resolution,[status(thm)],[c_26,c_4498])).

tff(c_4535,plain,(
    ! [B_724] :
      ( r6_binop_1('#skF_2',B_724,'#skF_6')
      | ~ r5_binop_1('#skF_2',B_724,'#skF_6')
      | ~ r4_binop_1('#skF_2',B_724,'#skF_6')
      | ~ m1_subset_1(B_724,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
      | ~ v1_funct_2(B_724,k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1(B_724) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_4502])).

tff(c_4541,plain,
    ( r6_binop_1('#skF_2','#skF_5','#skF_6')
    | ~ r5_binop_1('#skF_2','#skF_5','#skF_6')
    | ~ r4_binop_1('#skF_2','#skF_5','#skF_6')
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_4535])).

tff(c_4547,plain,
    ( r6_binop_1('#skF_2','#skF_5','#skF_6')
    | ~ r5_binop_1('#skF_2','#skF_5','#skF_6')
    | ~ r4_binop_1('#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_4541])).

tff(c_4548,plain,
    ( ~ r5_binop_1('#skF_2','#skF_5','#skF_6')
    | ~ r4_binop_1('#skF_2','#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_4355,c_4547])).

tff(c_4549,plain,(
    ~ r4_binop_1('#skF_2','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_4548])).

tff(c_4357,plain,(
    ! [A_698,B_699,C_700,D_701] :
      ( v1_funct_1(k6_filter_1(A_698,B_699,C_700,D_701))
      | ~ m1_subset_1(D_701,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_699,B_699),B_699)))
      | ~ v1_funct_2(D_701,k2_zfmisc_1(B_699,B_699),B_699)
      | ~ v1_funct_1(D_701)
      | ~ m1_subset_1(C_700,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_698,A_698),A_698)))
      | ~ v1_funct_2(C_700,k2_zfmisc_1(A_698,A_698),A_698)
      | ~ v1_funct_1(C_700) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4361,plain,(
    ! [A_698,C_700] :
      ( v1_funct_1(k6_filter_1(A_698,'#skF_2',C_700,'#skF_6'))
      | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_700,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_698,A_698),A_698)))
      | ~ v1_funct_2(C_700,k2_zfmisc_1(A_698,A_698),A_698)
      | ~ v1_funct_1(C_700) ) ),
    inference(resolution,[status(thm)],[c_26,c_4357])).

tff(c_4437,plain,(
    ! [A_709,C_710] :
      ( v1_funct_1(k6_filter_1(A_709,'#skF_2',C_710,'#skF_6'))
      | ~ m1_subset_1(C_710,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_709,A_709),A_709)))
      | ~ v1_funct_2(C_710,k2_zfmisc_1(A_709,A_709),A_709)
      | ~ v1_funct_1(C_710) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_4361])).

tff(c_4446,plain,
    ( v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_4437])).

tff(c_4458,plain,(
    v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_4446])).

tff(c_4365,plain,(
    ! [A_698,C_700] :
      ( v1_funct_1(k6_filter_1(A_698,'#skF_2',C_700,'#skF_5'))
      | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_700,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_698,A_698),A_698)))
      | ~ v1_funct_2(C_700,k2_zfmisc_1(A_698,A_698),A_698)
      | ~ v1_funct_1(C_700) ) ),
    inference(resolution,[status(thm)],[c_32,c_4357])).

tff(c_4403,plain,(
    ! [A_704,C_705] :
      ( v1_funct_1(k6_filter_1(A_704,'#skF_2',C_705,'#skF_5'))
      | ~ m1_subset_1(C_705,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_704,A_704),A_704)))
      | ~ v1_funct_2(C_705,k2_zfmisc_1(A_704,A_704),A_704)
      | ~ v1_funct_1(C_705) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_4365])).

tff(c_4406,plain,
    ( v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_4403])).

tff(c_4418,plain,(
    v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_4406])).

tff(c_4428,plain,(
    ! [A_706,B_707,C_708] :
      ( r4_binop_1(A_706,B_707,C_708)
      | ~ r6_binop_1(A_706,B_707,C_708)
      | ~ m1_subset_1(C_708,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_706,A_706),A_706)))
      | ~ v1_funct_2(C_708,k2_zfmisc_1(A_706,A_706),A_706)
      | ~ v1_funct_1(C_708)
      | ~ m1_subset_1(B_707,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_706,A_706),A_706)))
      | ~ v1_funct_2(B_707,k2_zfmisc_1(A_706,A_706),A_706)
      | ~ v1_funct_1(B_707) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4436,plain,
    ( r4_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_65,c_4428])).

tff(c_4752,plain,
    ( r4_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4418,c_4458,c_4436])).

tff(c_4753,plain,(
    ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4752])).

tff(c_4756,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_4753])).

tff(c_4760,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_36,c_34,c_32,c_4756])).

tff(c_4761,plain,
    ( ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | r4_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_4752])).

tff(c_5219,plain,(
    ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_4761])).

tff(c_5222,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_5219])).

tff(c_5226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_30,c_28,c_26,c_5222])).

tff(c_5228,plain,(
    m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_4761])).

tff(c_4363,plain,(
    ! [A_698,C_700] :
      ( v1_funct_1(k6_filter_1(A_698,'#skF_1',C_700,'#skF_4'))
      | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(C_700,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_698,A_698),A_698)))
      | ~ v1_funct_2(C_700,k2_zfmisc_1(A_698,A_698),A_698)
      | ~ v1_funct_1(C_700) ) ),
    inference(resolution,[status(thm)],[c_38,c_4357])).

tff(c_4374,plain,(
    ! [A_698,C_700] :
      ( v1_funct_1(k6_filter_1(A_698,'#skF_1',C_700,'#skF_4'))
      | ~ m1_subset_1(C_700,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_698,A_698),A_698)))
      | ~ v1_funct_2(C_700,k2_zfmisc_1(A_698,A_698),A_698)
      | ~ v1_funct_1(C_700) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_4363])).

tff(c_5285,plain,
    ( v1_funct_1(k6_filter_1(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_1',k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),'#skF_4'))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_5228,c_4374])).

tff(c_5359,plain,
    ( v1_funct_1(k6_filter_1(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_1',k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),'#skF_4'))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4458,c_5285])).

tff(c_5372,plain,(
    ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_5359])).

tff(c_5410,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_5372])).

tff(c_5414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_30,c_28,c_26,c_5410])).

tff(c_5416,plain,(
    v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_5359])).

tff(c_5227,plain,
    ( ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | r4_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_4761])).

tff(c_5417,plain,(
    ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_5227])).

tff(c_5431,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_5417])).

tff(c_5435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_36,c_34,c_32,c_5431])).

tff(c_5436,plain,
    ( ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | r4_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_5227])).

tff(c_5675,plain,(
    r4_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5416,c_5436])).

tff(c_16,plain,(
    ! [F_71,C_57,E_69,D_65,B_41,A_9] :
      ( r4_binop_1(B_41,E_69,F_71)
      | ~ r4_binop_1(k2_zfmisc_1(A_9,B_41),k6_filter_1(A_9,B_41,C_57,E_69),k6_filter_1(A_9,B_41,D_65,F_71))
      | ~ m1_subset_1(F_71,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_41,B_41),B_41)))
      | ~ v1_funct_2(F_71,k2_zfmisc_1(B_41,B_41),B_41)
      | ~ v1_funct_1(F_71)
      | ~ m1_subset_1(E_69,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_41,B_41),B_41)))
      | ~ v1_funct_2(E_69,k2_zfmisc_1(B_41,B_41),B_41)
      | ~ v1_funct_1(E_69)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9,A_9),A_9)))
      | ~ v1_funct_2(D_65,k2_zfmisc_1(A_9,A_9),A_9)
      | ~ v1_funct_1(D_65)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9,A_9),A_9)))
      | ~ v1_funct_2(C_57,k2_zfmisc_1(A_9,A_9),A_9)
      | ~ v1_funct_1(C_57)
      | v1_xboole_0(B_41)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5678,plain,
    ( r4_binop_1('#skF_2','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_5675,c_16])).

tff(c_5684,plain,
    ( r4_binop_1('#skF_2','#skF_5','#skF_6')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_38,c_36,c_34,c_32,c_30,c_28,c_26,c_5678])).

tff(c_5686,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_4549,c_5684])).

tff(c_5687,plain,(
    ~ r5_binop_1('#skF_2','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_4548])).

tff(c_5743,plain,
    ( r4_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4418,c_4458,c_4436])).

tff(c_5744,plain,(
    ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_5743])).

tff(c_5747,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_5744])).

tff(c_5751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_36,c_34,c_32,c_5747])).

tff(c_5753,plain,(
    v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_5743])).

tff(c_5752,plain,
    ( ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | r4_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_5743])).

tff(c_6399,plain,(
    ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_5752])).

tff(c_6402,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_6399])).

tff(c_6406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_30,c_28,c_26,c_6402])).

tff(c_6408,plain,(
    m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_5752])).

tff(c_4359,plain,(
    ! [A_698,C_700] :
      ( v1_funct_1(k6_filter_1(A_698,'#skF_1',C_700,'#skF_3'))
      | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_700,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_698,A_698),A_698)))
      | ~ v1_funct_2(C_700,k2_zfmisc_1(A_698,A_698),A_698)
      | ~ v1_funct_1(C_700) ) ),
    inference(resolution,[status(thm)],[c_44,c_4357])).

tff(c_4368,plain,(
    ! [A_698,C_700] :
      ( v1_funct_1(k6_filter_1(A_698,'#skF_1',C_700,'#skF_3'))
      | ~ m1_subset_1(C_700,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_698,A_698),A_698)))
      | ~ v1_funct_2(C_700,k2_zfmisc_1(A_698,A_698),A_698)
      | ~ v1_funct_1(C_700) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_4359])).

tff(c_6512,plain,
    ( v1_funct_1(k6_filter_1(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_1',k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),'#skF_3'))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_6408,c_4368])).

tff(c_6595,plain,
    ( v1_funct_1(k6_filter_1(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_1',k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),'#skF_3'))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4458,c_6512])).

tff(c_6599,plain,(
    ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_6595])).

tff(c_6603,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_6599])).

tff(c_6607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_30,c_28,c_26,c_6603])).

tff(c_6609,plain,(
    v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_6595])).

tff(c_6407,plain,
    ( ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | r4_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_5752])).

tff(c_6657,plain,
    ( ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | r4_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6609,c_6407])).

tff(c_6658,plain,(
    ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_6657])).

tff(c_6661,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_6658])).

tff(c_6665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_36,c_34,c_32,c_6661])).

tff(c_6667,plain,(
    m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_6657])).

tff(c_4462,plain,(
    ! [A_711,B_712,C_713] :
      ( r5_binop_1(A_711,B_712,C_713)
      | ~ r6_binop_1(A_711,B_712,C_713)
      | ~ m1_subset_1(C_713,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_711,A_711),A_711)))
      | ~ v1_funct_2(C_713,k2_zfmisc_1(A_711,A_711),A_711)
      | ~ v1_funct_1(C_713)
      | ~ m1_subset_1(B_712,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_711,A_711),A_711)))
      | ~ v1_funct_2(B_712,k2_zfmisc_1(A_711,A_711),A_711)
      | ~ v1_funct_1(B_712) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4466,plain,
    ( r5_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_65,c_4462])).

tff(c_4472,plain,
    ( r5_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ m1_subset_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2'))))
    | ~ v1_funct_2(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4418,c_4466])).

tff(c_6884,plain,(
    r5_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5753,c_6667,c_4458,c_6609,c_6408,c_4472])).

tff(c_22,plain,(
    ! [B_104,E_132,F_134,A_72,C_120,D_128] :
      ( r5_binop_1(B_104,E_132,F_134)
      | ~ r5_binop_1(k2_zfmisc_1(A_72,B_104),k6_filter_1(A_72,B_104,C_120,E_132),k6_filter_1(A_72,B_104,D_128,F_134))
      | ~ m1_subset_1(F_134,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_104,B_104),B_104)))
      | ~ v1_funct_2(F_134,k2_zfmisc_1(B_104,B_104),B_104)
      | ~ v1_funct_1(F_134)
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_104,B_104),B_104)))
      | ~ v1_funct_2(E_132,k2_zfmisc_1(B_104,B_104),B_104)
      | ~ v1_funct_1(E_132)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_72,A_72),A_72)))
      | ~ v1_funct_2(D_128,k2_zfmisc_1(A_72,A_72),A_72)
      | ~ v1_funct_1(D_128)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_72,A_72),A_72)))
      | ~ v1_funct_2(C_120,k2_zfmisc_1(A_72,A_72),A_72)
      | ~ v1_funct_1(C_120)
      | v1_xboole_0(B_104)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_6887,plain,
    ( r5_binop_1('#skF_2','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6884,c_22])).

tff(c_6893,plain,
    ( r5_binop_1('#skF_2','#skF_5','#skF_6')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_38,c_36,c_34,c_32,c_30,c_28,c_26,c_6887])).

tff(c_6895,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_5687,c_6893])).

tff(c_6897,plain,(
    ~ r6_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_64,plain,
    ( r6_binop_1('#skF_1','#skF_3','#skF_4')
    | r6_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_6898,plain,(
    r6_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_6897,c_64])).

tff(c_7008,plain,(
    ! [A_993,B_994,C_995] :
      ( r5_binop_1(A_993,B_994,C_995)
      | ~ r6_binop_1(A_993,B_994,C_995)
      | ~ m1_subset_1(C_995,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_993,A_993),A_993)))
      | ~ v1_funct_2(C_995,k2_zfmisc_1(A_993,A_993),A_993)
      | ~ v1_funct_1(C_995)
      | ~ m1_subset_1(B_994,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_993,A_993),A_993)))
      | ~ v1_funct_2(B_994,k2_zfmisc_1(A_993,A_993),A_993)
      | ~ v1_funct_1(B_994) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_7010,plain,
    ( r5_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6898,c_7008])).

tff(c_7015,plain,(
    r5_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_38,c_7010])).

tff(c_6896,plain,(
    r6_binop_1('#skF_2','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_7012,plain,
    ( r5_binop_1('#skF_2','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6896,c_7008])).

tff(c_7018,plain,(
    r5_binop_1('#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_28,c_26,c_7012])).

tff(c_20,plain,(
    ! [B_104,E_132,F_134,A_72,C_120,D_128] :
      ( r5_binop_1(k2_zfmisc_1(A_72,B_104),k6_filter_1(A_72,B_104,C_120,E_132),k6_filter_1(A_72,B_104,D_128,F_134))
      | ~ r5_binop_1(B_104,E_132,F_134)
      | ~ r5_binop_1(A_72,C_120,D_128)
      | ~ m1_subset_1(F_134,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_104,B_104),B_104)))
      | ~ v1_funct_2(F_134,k2_zfmisc_1(B_104,B_104),B_104)
      | ~ v1_funct_1(F_134)
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_104,B_104),B_104)))
      | ~ v1_funct_2(E_132,k2_zfmisc_1(B_104,B_104),B_104)
      | ~ v1_funct_1(E_132)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_72,A_72),A_72)))
      | ~ v1_funct_2(D_128,k2_zfmisc_1(A_72,A_72),A_72)
      | ~ v1_funct_1(D_128)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_72,A_72),A_72)))
      | ~ v1_funct_2(C_120,k2_zfmisc_1(A_72,A_72),A_72)
      | ~ v1_funct_1(C_120)
      | v1_xboole_0(B_104)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_6947,plain,(
    ! [A_986,B_987,C_988] :
      ( r4_binop_1(A_986,B_987,C_988)
      | ~ r6_binop_1(A_986,B_987,C_988)
      | ~ m1_subset_1(C_988,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_986,A_986),A_986)))
      | ~ v1_funct_2(C_988,k2_zfmisc_1(A_986,A_986),A_986)
      | ~ v1_funct_1(C_988)
      | ~ m1_subset_1(B_987,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_986,A_986),A_986)))
      | ~ v1_funct_2(B_987,k2_zfmisc_1(A_986,A_986),A_986)
      | ~ v1_funct_1(B_987) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6949,plain,
    ( r4_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6898,c_6947])).

tff(c_6954,plain,(
    r4_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_38,c_6949])).

tff(c_6951,plain,
    ( r4_binop_1('#skF_2','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6896,c_6947])).

tff(c_6957,plain,(
    r4_binop_1('#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_28,c_26,c_6951])).

tff(c_14,plain,(
    ! [F_71,C_57,E_69,D_65,B_41,A_9] :
      ( r4_binop_1(k2_zfmisc_1(A_9,B_41),k6_filter_1(A_9,B_41,C_57,E_69),k6_filter_1(A_9,B_41,D_65,F_71))
      | ~ r4_binop_1(B_41,E_69,F_71)
      | ~ r4_binop_1(A_9,C_57,D_65)
      | ~ m1_subset_1(F_71,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_41,B_41),B_41)))
      | ~ v1_funct_2(F_71,k2_zfmisc_1(B_41,B_41),B_41)
      | ~ v1_funct_1(F_71)
      | ~ m1_subset_1(E_69,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_41,B_41),B_41)))
      | ~ v1_funct_2(E_69,k2_zfmisc_1(B_41,B_41),B_41)
      | ~ v1_funct_1(E_69)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9,A_9),A_9)))
      | ~ v1_funct_2(D_65,k2_zfmisc_1(A_9,A_9),A_9)
      | ~ v1_funct_1(D_65)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9,A_9),A_9)))
      | ~ v1_funct_2(C_57,k2_zfmisc_1(A_9,A_9),A_9)
      | ~ v1_funct_1(C_57)
      | v1_xboole_0(B_41)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6901,plain,(
    ! [A_980,B_981,C_982,D_983] :
      ( v1_funct_1(k6_filter_1(A_980,B_981,C_982,D_983))
      | ~ m1_subset_1(D_983,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_981,B_981),B_981)))
      | ~ v1_funct_2(D_983,k2_zfmisc_1(B_981,B_981),B_981)
      | ~ v1_funct_1(D_983)
      | ~ m1_subset_1(C_982,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_980,A_980),A_980)))
      | ~ v1_funct_2(C_982,k2_zfmisc_1(A_980,A_980),A_980)
      | ~ v1_funct_1(C_982) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6909,plain,(
    ! [A_980,C_982] :
      ( v1_funct_1(k6_filter_1(A_980,'#skF_2',C_982,'#skF_5'))
      | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_982,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_980,A_980),A_980)))
      | ~ v1_funct_2(C_982,k2_zfmisc_1(A_980,A_980),A_980)
      | ~ v1_funct_1(C_982) ) ),
    inference(resolution,[status(thm)],[c_32,c_6901])).

tff(c_6983,plain,(
    ! [A_991,C_992] :
      ( v1_funct_1(k6_filter_1(A_991,'#skF_2',C_992,'#skF_5'))
      | ~ m1_subset_1(C_992,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_991,A_991),A_991)))
      | ~ v1_funct_2(C_992,k2_zfmisc_1(A_991,A_991),A_991)
      | ~ v1_funct_1(C_992) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_6909])).

tff(c_6986,plain,
    ( v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_6983])).

tff(c_6998,plain,(
    v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_6986])).

tff(c_6905,plain,(
    ! [A_980,C_982] :
      ( v1_funct_1(k6_filter_1(A_980,'#skF_2',C_982,'#skF_6'))
      | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_982,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_980,A_980),A_980)))
      | ~ v1_funct_2(C_982,k2_zfmisc_1(A_980,A_980),A_980)
      | ~ v1_funct_1(C_982) ) ),
    inference(resolution,[status(thm)],[c_26,c_6901])).

tff(c_6958,plain,(
    ! [A_989,C_990] :
      ( v1_funct_1(k6_filter_1(A_989,'#skF_2',C_990,'#skF_6'))
      | ~ m1_subset_1(C_990,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_989,A_989),A_989)))
      | ~ v1_funct_2(C_990,k2_zfmisc_1(A_989,A_989),A_989)
      | ~ v1_funct_1(C_990) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_6905])).

tff(c_6967,plain,
    ( v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_6958])).

tff(c_6979,plain,(
    v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_6967])).

tff(c_7124,plain,(
    ! [A_1009,B_1010,C_1011,D_1012] :
      ( m1_subset_1(k6_filter_1(A_1009,B_1010,C_1011,D_1012),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1009,B_1010),k2_zfmisc_1(A_1009,B_1010)),k2_zfmisc_1(A_1009,B_1010))))
      | ~ m1_subset_1(D_1012,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_1010,B_1010),B_1010)))
      | ~ v1_funct_2(D_1012,k2_zfmisc_1(B_1010,B_1010),B_1010)
      | ~ v1_funct_1(D_1012)
      | ~ m1_subset_1(C_1011,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1009,A_1009),A_1009)))
      | ~ v1_funct_2(C_1011,k2_zfmisc_1(A_1009,A_1009),A_1009)
      | ~ v1_funct_1(C_1011) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [A_1,B_2,C_4] :
      ( r6_binop_1(A_1,B_2,C_4)
      | ~ r5_binop_1(A_1,B_2,C_4)
      | ~ r4_binop_1(A_1,B_2,C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1,A_1),A_1)))
      | ~ v1_funct_2(C_4,k2_zfmisc_1(A_1,A_1),A_1)
      | ~ v1_funct_1(C_4)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1,A_1),A_1)))
      | ~ v1_funct_2(B_2,k2_zfmisc_1(A_1,A_1),A_1)
      | ~ v1_funct_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_7666,plain,(
    ! [B_1115,A_1113,C_1114,D_1117,B_1116] :
      ( r6_binop_1(k2_zfmisc_1(A_1113,B_1115),B_1116,k6_filter_1(A_1113,B_1115,C_1114,D_1117))
      | ~ r5_binop_1(k2_zfmisc_1(A_1113,B_1115),B_1116,k6_filter_1(A_1113,B_1115,C_1114,D_1117))
      | ~ r4_binop_1(k2_zfmisc_1(A_1113,B_1115),B_1116,k6_filter_1(A_1113,B_1115,C_1114,D_1117))
      | ~ v1_funct_2(k6_filter_1(A_1113,B_1115,C_1114,D_1117),k2_zfmisc_1(k2_zfmisc_1(A_1113,B_1115),k2_zfmisc_1(A_1113,B_1115)),k2_zfmisc_1(A_1113,B_1115))
      | ~ v1_funct_1(k6_filter_1(A_1113,B_1115,C_1114,D_1117))
      | ~ m1_subset_1(B_1116,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1113,B_1115),k2_zfmisc_1(A_1113,B_1115)),k2_zfmisc_1(A_1113,B_1115))))
      | ~ v1_funct_2(B_1116,k2_zfmisc_1(k2_zfmisc_1(A_1113,B_1115),k2_zfmisc_1(A_1113,B_1115)),k2_zfmisc_1(A_1113,B_1115))
      | ~ v1_funct_1(B_1116)
      | ~ m1_subset_1(D_1117,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_1115,B_1115),B_1115)))
      | ~ v1_funct_2(D_1117,k2_zfmisc_1(B_1115,B_1115),B_1115)
      | ~ v1_funct_1(D_1117)
      | ~ m1_subset_1(C_1114,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1113,A_1113),A_1113)))
      | ~ v1_funct_2(C_1114,k2_zfmisc_1(A_1113,A_1113),A_1113)
      | ~ v1_funct_1(C_1114) ) ),
    inference(resolution,[status(thm)],[c_7124,c_2])).

tff(c_7834,plain,(
    ! [B_1137,A_1140,C_1139,B_1138,D_1136] :
      ( r6_binop_1(k2_zfmisc_1(A_1140,B_1138),B_1137,k6_filter_1(A_1140,B_1138,C_1139,D_1136))
      | ~ r5_binop_1(k2_zfmisc_1(A_1140,B_1138),B_1137,k6_filter_1(A_1140,B_1138,C_1139,D_1136))
      | ~ r4_binop_1(k2_zfmisc_1(A_1140,B_1138),B_1137,k6_filter_1(A_1140,B_1138,C_1139,D_1136))
      | ~ v1_funct_1(k6_filter_1(A_1140,B_1138,C_1139,D_1136))
      | ~ m1_subset_1(B_1137,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1140,B_1138),k2_zfmisc_1(A_1140,B_1138)),k2_zfmisc_1(A_1140,B_1138))))
      | ~ v1_funct_2(B_1137,k2_zfmisc_1(k2_zfmisc_1(A_1140,B_1138),k2_zfmisc_1(A_1140,B_1138)),k2_zfmisc_1(A_1140,B_1138))
      | ~ v1_funct_1(B_1137)
      | ~ m1_subset_1(D_1136,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_1138,B_1138),B_1138)))
      | ~ v1_funct_2(D_1136,k2_zfmisc_1(B_1138,B_1138),B_1138)
      | ~ v1_funct_1(D_1136)
      | ~ m1_subset_1(C_1139,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1140,A_1140),A_1140)))
      | ~ v1_funct_2(C_1139,k2_zfmisc_1(A_1140,A_1140),A_1140)
      | ~ v1_funct_1(C_1139) ) ),
    inference(resolution,[status(thm)],[c_10,c_7666])).

tff(c_8175,plain,(
    ! [B_1180,D_1179,C_1181,A_1183,C_1182,D_1184] :
      ( r6_binop_1(k2_zfmisc_1(A_1183,B_1180),k6_filter_1(A_1183,B_1180,C_1182,D_1179),k6_filter_1(A_1183,B_1180,C_1181,D_1184))
      | ~ r5_binop_1(k2_zfmisc_1(A_1183,B_1180),k6_filter_1(A_1183,B_1180,C_1182,D_1179),k6_filter_1(A_1183,B_1180,C_1181,D_1184))
      | ~ r4_binop_1(k2_zfmisc_1(A_1183,B_1180),k6_filter_1(A_1183,B_1180,C_1182,D_1179),k6_filter_1(A_1183,B_1180,C_1181,D_1184))
      | ~ v1_funct_1(k6_filter_1(A_1183,B_1180,C_1181,D_1184))
      | ~ v1_funct_2(k6_filter_1(A_1183,B_1180,C_1182,D_1179),k2_zfmisc_1(k2_zfmisc_1(A_1183,B_1180),k2_zfmisc_1(A_1183,B_1180)),k2_zfmisc_1(A_1183,B_1180))
      | ~ v1_funct_1(k6_filter_1(A_1183,B_1180,C_1182,D_1179))
      | ~ m1_subset_1(D_1184,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_1180,B_1180),B_1180)))
      | ~ v1_funct_2(D_1184,k2_zfmisc_1(B_1180,B_1180),B_1180)
      | ~ v1_funct_1(D_1184)
      | ~ m1_subset_1(C_1181,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1183,A_1183),A_1183)))
      | ~ v1_funct_2(C_1181,k2_zfmisc_1(A_1183,A_1183),A_1183)
      | ~ v1_funct_1(C_1181)
      | ~ m1_subset_1(D_1179,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_1180,B_1180),B_1180)))
      | ~ v1_funct_2(D_1179,k2_zfmisc_1(B_1180,B_1180),B_1180)
      | ~ v1_funct_1(D_1179)
      | ~ m1_subset_1(C_1182,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1183,A_1183),A_1183)))
      | ~ v1_funct_2(C_1182,k2_zfmisc_1(A_1183,A_1183),A_1183)
      | ~ v1_funct_1(C_1182) ) ),
    inference(resolution,[status(thm)],[c_8,c_7834])).

tff(c_8904,plain,(
    ! [B_1330,D_1334,C_1332,C_1331,A_1333,D_1329] :
      ( r6_binop_1(k2_zfmisc_1(A_1333,B_1330),k6_filter_1(A_1333,B_1330,C_1332,D_1329),k6_filter_1(A_1333,B_1330,C_1331,D_1334))
      | ~ r5_binop_1(k2_zfmisc_1(A_1333,B_1330),k6_filter_1(A_1333,B_1330,C_1332,D_1329),k6_filter_1(A_1333,B_1330,C_1331,D_1334))
      | ~ r4_binop_1(k2_zfmisc_1(A_1333,B_1330),k6_filter_1(A_1333,B_1330,C_1332,D_1329),k6_filter_1(A_1333,B_1330,C_1331,D_1334))
      | ~ v1_funct_1(k6_filter_1(A_1333,B_1330,C_1331,D_1334))
      | ~ v1_funct_1(k6_filter_1(A_1333,B_1330,C_1332,D_1329))
      | ~ m1_subset_1(D_1334,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_1330,B_1330),B_1330)))
      | ~ v1_funct_2(D_1334,k2_zfmisc_1(B_1330,B_1330),B_1330)
      | ~ v1_funct_1(D_1334)
      | ~ m1_subset_1(C_1331,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1333,A_1333),A_1333)))
      | ~ v1_funct_2(C_1331,k2_zfmisc_1(A_1333,A_1333),A_1333)
      | ~ v1_funct_1(C_1331)
      | ~ m1_subset_1(D_1329,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_1330,B_1330),B_1330)))
      | ~ v1_funct_2(D_1329,k2_zfmisc_1(B_1330,B_1330),B_1330)
      | ~ v1_funct_1(D_1329)
      | ~ m1_subset_1(C_1332,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1333,A_1333),A_1333)))
      | ~ v1_funct_2(C_1332,k2_zfmisc_1(A_1333,A_1333),A_1333)
      | ~ v1_funct_1(C_1332) ) ),
    inference(resolution,[status(thm)],[c_10,c_8175])).

tff(c_8911,plain,
    ( ~ r5_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ r4_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ v1_funct_1(k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8904,c_6897])).

tff(c_8916,plain,
    ( ~ r5_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6'))
    | ~ r4_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_36,c_34,c_32,c_42,c_40,c_38,c_30,c_28,c_26,c_6998,c_6979,c_8911])).

tff(c_8917,plain,(
    ~ r4_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_8916])).

tff(c_8920,plain,
    ( ~ r4_binop_1('#skF_2','#skF_5','#skF_6')
    | ~ r4_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_8917])).

tff(c_8923,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_38,c_36,c_34,c_32,c_30,c_28,c_26,c_6954,c_6957,c_8920])).

tff(c_8925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_8923])).

tff(c_8926,plain,(
    ~ r5_binop_1(k2_zfmisc_1('#skF_1','#skF_2'),k6_filter_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_filter_1('#skF_1','#skF_2','#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_8916])).

tff(c_8930,plain,
    ( ~ r5_binop_1('#skF_2','#skF_5','#skF_6')
    | ~ r5_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_6',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_3',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_8926])).

tff(c_8933,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_38,c_36,c_34,c_32,c_30,c_28,c_26,c_7015,c_7018,c_8930])).

tff(c_8935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_8933])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:54:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.14/4.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.14/4.37  
% 10.14/4.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.14/4.37  %$ v1_funct_2 > r6_binop_1 > r5_binop_1 > r4_binop_1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k6_filter_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.14/4.37  
% 10.14/4.37  %Foreground sorts:
% 10.14/4.37  
% 10.14/4.37  
% 10.14/4.37  %Background operators:
% 10.14/4.37  
% 10.14/4.37  
% 10.14/4.37  %Foreground operators:
% 10.14/4.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.14/4.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.14/4.37  tff(r6_binop_1, type, r6_binop_1: ($i * $i * $i) > $o).
% 10.14/4.37  tff('#skF_5', type, '#skF_5': $i).
% 10.14/4.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.14/4.37  tff('#skF_6', type, '#skF_6': $i).
% 10.14/4.37  tff('#skF_2', type, '#skF_2': $i).
% 10.14/4.37  tff('#skF_3', type, '#skF_3': $i).
% 10.14/4.37  tff('#skF_1', type, '#skF_1': $i).
% 10.14/4.37  tff(k6_filter_1, type, k6_filter_1: ($i * $i * $i * $i) > $i).
% 10.14/4.37  tff(r4_binop_1, type, r4_binop_1: ($i * $i * $i) > $o).
% 10.14/4.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.14/4.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.14/4.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.14/4.37  tff('#skF_4', type, '#skF_4': $i).
% 10.14/4.37  tff(r5_binop_1, type, r5_binop_1: ($i * $i * $i) > $o).
% 10.14/4.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.14/4.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.14/4.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.14/4.37  
% 10.39/4.41  tff(f_186, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, k2_zfmisc_1(A, A), A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, k2_zfmisc_1(B, B), B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B, B), B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, k2_zfmisc_1(B, B), B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B, B), B)))) => ((r6_binop_1(A, C, D) & r6_binop_1(B, E, F)) <=> r6_binop_1(k2_zfmisc_1(A, B), k6_filter_1(A, B, C, E), k6_filter_1(A, B, D, F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_filter_1)).
% 10.39/4.41  tff(f_44, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, k2_zfmisc_1(A, A), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => (r6_binop_1(A, B, C) <=> (r4_binop_1(A, B, C) & r5_binop_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_binop_1)).
% 10.39/4.41  tff(f_62, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) & v1_funct_1(D)) & v1_funct_2(D, k2_zfmisc_1(B, B), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B, B), B)))) => ((v1_funct_1(k6_filter_1(A, B, C, D)) & v1_funct_2(k6_filter_1(A, B, C, D), k2_zfmisc_1(k2_zfmisc_1(A, B), k2_zfmisc_1(A, B)), k2_zfmisc_1(A, B))) & m1_subset_1(k6_filter_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, B), k2_zfmisc_1(A, B)), k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_filter_1)).
% 10.39/4.41  tff(f_103, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, k2_zfmisc_1(A, A), A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, k2_zfmisc_1(B, B), B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B, B), B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, k2_zfmisc_1(B, B), B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B, B), B)))) => ((r4_binop_1(A, C, D) & r4_binop_1(B, E, F)) <=> r4_binop_1(k2_zfmisc_1(A, B), k6_filter_1(A, B, C, E), k6_filter_1(A, B, D, F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_filter_1)).
% 10.39/4.41  tff(f_144, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, k2_zfmisc_1(A, A), A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, k2_zfmisc_1(B, B), B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B, B), B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, k2_zfmisc_1(B, B), B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B, B), B)))) => ((r5_binop_1(A, C, D) & r5_binop_1(B, E, F)) <=> r5_binop_1(k2_zfmisc_1(A, B), k6_filter_1(A, B, C, E), k6_filter_1(A, B, D, F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_filter_1)).
% 10.39/4.41  tff(c_52, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 10.39/4.41  tff(c_50, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 10.39/4.41  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_186])).
% 10.39/4.41  tff(c_46, plain, (v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 10.39/4.41  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 10.39/4.41  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_186])).
% 10.39/4.41  tff(c_40, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 10.39/4.41  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 10.39/4.41  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 10.39/4.41  tff(c_34, plain, (v1_funct_2('#skF_5', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 10.39/4.41  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 10.39/4.41  tff(c_30, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_186])).
% 10.39/4.41  tff(c_28, plain, (v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 10.39/4.41  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 10.39/4.41  tff(c_62, plain, (r6_binop_1('#skF_2', '#skF_5', '#skF_6') | r6_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 10.39/4.41  tff(c_65, plain, (r6_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(splitLeft, [status(thm)], [c_62])).
% 10.39/4.41  tff(c_54, plain, (~r6_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~r6_binop_1('#skF_2', '#skF_5', '#skF_6') | ~r6_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_186])).
% 10.39/4.41  tff(c_68, plain, (~r6_binop_1('#skF_2', '#skF_5', '#skF_6') | ~r6_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_54])).
% 10.39/4.41  tff(c_69, plain, (~r6_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_68])).
% 10.39/4.41  tff(c_199, plain, (![A_210, B_211, C_212]: (r6_binop_1(A_210, B_211, C_212) | ~r5_binop_1(A_210, B_211, C_212) | ~r4_binop_1(A_210, B_211, C_212) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_210, A_210), A_210))) | ~v1_funct_2(C_212, k2_zfmisc_1(A_210, A_210), A_210) | ~v1_funct_1(C_212) | ~m1_subset_1(B_211, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_210, A_210), A_210))) | ~v1_funct_2(B_211, k2_zfmisc_1(A_210, A_210), A_210) | ~v1_funct_1(B_211))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.39/4.41  tff(c_205, plain, (![B_211]: (r6_binop_1('#skF_1', B_211, '#skF_4') | ~r5_binop_1('#skF_1', B_211, '#skF_4') | ~r4_binop_1('#skF_1', B_211, '#skF_4') | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1(B_211, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(B_211, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(B_211))), inference(resolution, [status(thm)], [c_38, c_199])).
% 10.39/4.41  tff(c_236, plain, (![B_218]: (r6_binop_1('#skF_1', B_218, '#skF_4') | ~r5_binop_1('#skF_1', B_218, '#skF_4') | ~r4_binop_1('#skF_1', B_218, '#skF_4') | ~m1_subset_1(B_218, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(B_218, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(B_218))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_205])).
% 10.39/4.41  tff(c_239, plain, (r6_binop_1('#skF_1', '#skF_3', '#skF_4') | ~r5_binop_1('#skF_1', '#skF_3', '#skF_4') | ~r4_binop_1('#skF_1', '#skF_3', '#skF_4') | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_236])).
% 10.39/4.41  tff(c_245, plain, (r6_binop_1('#skF_1', '#skF_3', '#skF_4') | ~r5_binop_1('#skF_1', '#skF_3', '#skF_4') | ~r4_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_239])).
% 10.39/4.41  tff(c_246, plain, (~r5_binop_1('#skF_1', '#skF_3', '#skF_4') | ~r4_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_69, c_245])).
% 10.39/4.41  tff(c_250, plain, (~r4_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_246])).
% 10.39/4.41  tff(c_8, plain, (![A_5, B_6, C_7, D_8]: (m1_subset_1(k6_filter_1(A_5, B_6, C_7, D_8), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_5, B_6), k2_zfmisc_1(A_5, B_6)), k2_zfmisc_1(A_5, B_6)))) | ~m1_subset_1(D_8, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_6, B_6), B_6))) | ~v1_funct_2(D_8, k2_zfmisc_1(B_6, B_6), B_6) | ~v1_funct_1(D_8) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_5, A_5), A_5))) | ~v1_funct_2(C_7, k2_zfmisc_1(A_5, A_5), A_5) | ~v1_funct_1(C_7))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.39/4.41  tff(c_70, plain, (![A_192, B_193, C_194, D_195]: (v1_funct_1(k6_filter_1(A_192, B_193, C_194, D_195)) | ~m1_subset_1(D_195, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_193, B_193), B_193))) | ~v1_funct_2(D_195, k2_zfmisc_1(B_193, B_193), B_193) | ~v1_funct_1(D_195) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_192, A_192), A_192))) | ~v1_funct_2(C_194, k2_zfmisc_1(A_192, A_192), A_192) | ~v1_funct_1(C_194))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.39/4.41  tff(c_78, plain, (![A_192, C_194]: (v1_funct_1(k6_filter_1(A_192, '#skF_2', C_194, '#skF_5')) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_192, A_192), A_192))) | ~v1_funct_2(C_194, k2_zfmisc_1(A_192, A_192), A_192) | ~v1_funct_1(C_194))), inference(resolution, [status(thm)], [c_32, c_70])).
% 10.39/4.41  tff(c_174, plain, (![A_208, C_209]: (v1_funct_1(k6_filter_1(A_208, '#skF_2', C_209, '#skF_5')) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_208, A_208), A_208))) | ~v1_funct_2(C_209, k2_zfmisc_1(A_208, A_208), A_208) | ~v1_funct_1(C_209))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_78])).
% 10.39/4.41  tff(c_177, plain, (v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_174])).
% 10.39/4.41  tff(c_189, plain, (v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_177])).
% 10.39/4.41  tff(c_10, plain, (![A_5, B_6, C_7, D_8]: (v1_funct_2(k6_filter_1(A_5, B_6, C_7, D_8), k2_zfmisc_1(k2_zfmisc_1(A_5, B_6), k2_zfmisc_1(A_5, B_6)), k2_zfmisc_1(A_5, B_6)) | ~m1_subset_1(D_8, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_6, B_6), B_6))) | ~v1_funct_2(D_8, k2_zfmisc_1(B_6, B_6), B_6) | ~v1_funct_1(D_8) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_5, A_5), A_5))) | ~v1_funct_2(C_7, k2_zfmisc_1(A_5, A_5), A_5) | ~v1_funct_1(C_7))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.39/4.41  tff(c_74, plain, (![A_192, C_194]: (v1_funct_1(k6_filter_1(A_192, '#skF_2', C_194, '#skF_6')) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_192, A_192), A_192))) | ~v1_funct_2(C_194, k2_zfmisc_1(A_192, A_192), A_192) | ~v1_funct_1(C_194))), inference(resolution, [status(thm)], [c_26, c_70])).
% 10.39/4.41  tff(c_145, plain, (![A_203, C_204]: (v1_funct_1(k6_filter_1(A_203, '#skF_2', C_204, '#skF_6')) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_203, A_203), A_203))) | ~v1_funct_2(C_204, k2_zfmisc_1(A_203, A_203), A_203) | ~v1_funct_1(C_204))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_74])).
% 10.39/4.41  tff(c_154, plain, (v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_145])).
% 10.39/4.41  tff(c_166, plain, (v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_154])).
% 10.39/4.41  tff(c_170, plain, (![A_205, B_206, C_207]: (r4_binop_1(A_205, B_206, C_207) | ~r6_binop_1(A_205, B_206, C_207) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_205, A_205), A_205))) | ~v1_funct_2(C_207, k2_zfmisc_1(A_205, A_205), A_205) | ~v1_funct_1(C_207) | ~m1_subset_1(B_206, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_205, A_205), A_205))) | ~v1_funct_2(B_206, k2_zfmisc_1(A_205, A_205), A_205) | ~v1_funct_1(B_206))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.39/4.41  tff(c_173, plain, (r4_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_65, c_170])).
% 10.39/4.41  tff(c_767, plain, (r4_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_166, c_173])).
% 10.39/4.41  tff(c_768, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_767])).
% 10.39/4.41  tff(c_774, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_768])).
% 10.39/4.41  tff(c_778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_36, c_34, c_32, c_774])).
% 10.39/4.41  tff(c_780, plain, (v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_767])).
% 10.39/4.41  tff(c_116, plain, (![A_198, B_199, C_200]: (r5_binop_1(A_198, B_199, C_200) | ~r6_binop_1(A_198, B_199, C_200) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_198, A_198), A_198))) | ~v1_funct_2(C_200, k2_zfmisc_1(A_198, A_198), A_198) | ~v1_funct_1(C_200) | ~m1_subset_1(B_199, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_198, A_198), A_198))) | ~v1_funct_2(B_199, k2_zfmisc_1(A_198, A_198), A_198) | ~v1_funct_1(B_199))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.39/4.41  tff(c_119, plain, (r5_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_65, c_116])).
% 10.39/4.41  tff(c_787, plain, (r5_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_780, c_166, c_119])).
% 10.39/4.41  tff(c_788, plain, (~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(splitLeft, [status(thm)], [c_787])).
% 10.39/4.41  tff(c_791, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_788])).
% 10.39/4.41  tff(c_795, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_36, c_34, c_32, c_791])).
% 10.39/4.41  tff(c_796, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | r5_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_787])).
% 10.39/4.41  tff(c_983, plain, (~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(splitLeft, [status(thm)], [c_796])).
% 10.39/4.41  tff(c_986, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_983])).
% 10.39/4.41  tff(c_990, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_30, c_28, c_26, c_986])).
% 10.39/4.41  tff(c_992, plain, (m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(splitRight, [status(thm)], [c_796])).
% 10.39/4.41  tff(c_991, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | r5_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_796])).
% 10.39/4.41  tff(c_1139, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_991])).
% 10.39/4.41  tff(c_1142, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_1139])).
% 10.39/4.41  tff(c_1146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_30, c_28, c_26, c_1142])).
% 10.39/4.41  tff(c_1148, plain, (v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_991])).
% 10.39/4.41  tff(c_797, plain, (m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(splitRight, [status(thm)], [c_787])).
% 10.39/4.41  tff(c_779, plain, (~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | r4_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_767])).
% 10.39/4.41  tff(c_1314, plain, (r4_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_992, c_1148, c_797, c_779])).
% 10.39/4.41  tff(c_18, plain, (![F_71, C_57, E_69, D_65, B_41, A_9]: (r4_binop_1(A_9, C_57, D_65) | ~r4_binop_1(k2_zfmisc_1(A_9, B_41), k6_filter_1(A_9, B_41, C_57, E_69), k6_filter_1(A_9, B_41, D_65, F_71)) | ~m1_subset_1(F_71, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_41, B_41), B_41))) | ~v1_funct_2(F_71, k2_zfmisc_1(B_41, B_41), B_41) | ~v1_funct_1(F_71) | ~m1_subset_1(E_69, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_41, B_41), B_41))) | ~v1_funct_2(E_69, k2_zfmisc_1(B_41, B_41), B_41) | ~v1_funct_1(E_69) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9, A_9), A_9))) | ~v1_funct_2(D_65, k2_zfmisc_1(A_9, A_9), A_9) | ~v1_funct_1(D_65) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9, A_9), A_9))) | ~v1_funct_2(C_57, k2_zfmisc_1(A_9, A_9), A_9) | ~v1_funct_1(C_57) | v1_xboole_0(B_41) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.39/4.41  tff(c_1317, plain, (r4_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_1314, c_18])).
% 10.39/4.41  tff(c_1323, plain, (r4_binop_1('#skF_1', '#skF_3', '#skF_4') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_38, c_36, c_34, c_32, c_30, c_28, c_26, c_1317])).
% 10.39/4.41  tff(c_1325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_250, c_1323])).
% 10.39/4.41  tff(c_1326, plain, (~r5_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_246])).
% 10.39/4.41  tff(c_3921, plain, (r4_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_166, c_173])).
% 10.39/4.41  tff(c_3922, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_3921])).
% 10.39/4.41  tff(c_3925, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_3922])).
% 10.39/4.41  tff(c_3929, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_36, c_34, c_32, c_3925])).
% 10.39/4.41  tff(c_3931, plain, (v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_3921])).
% 10.39/4.41  tff(c_3967, plain, (r5_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_3931, c_166, c_119])).
% 10.39/4.41  tff(c_3968, plain, (~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(splitLeft, [status(thm)], [c_3967])).
% 10.39/4.41  tff(c_3971, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_3968])).
% 10.39/4.41  tff(c_3975, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_36, c_34, c_32, c_3971])).
% 10.39/4.41  tff(c_3976, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | r5_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_3967])).
% 10.39/4.41  tff(c_4125, plain, (~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(splitLeft, [status(thm)], [c_3976])).
% 10.39/4.41  tff(c_4128, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_4125])).
% 10.39/4.41  tff(c_4132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_30, c_28, c_26, c_4128])).
% 10.39/4.41  tff(c_4134, plain, (m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(splitRight, [status(thm)], [c_3976])).
% 10.39/4.41  tff(c_84, plain, (![A_192, C_194]: (v1_funct_1(k6_filter_1(A_192, '#skF_2', C_194, '#skF_6')) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_192, A_192), A_192))) | ~v1_funct_2(C_194, k2_zfmisc_1(A_192, A_192), A_192) | ~v1_funct_1(C_194))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_74])).
% 10.39/4.41  tff(c_4187, plain, (v1_funct_1(k6_filter_1(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_2', k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), '#skF_6')) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_4134, c_84])).
% 10.39/4.41  tff(c_4252, plain, (v1_funct_1(k6_filter_1(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_2', k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), '#skF_6')) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_4187])).
% 10.39/4.41  tff(c_4262, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_4252])).
% 10.39/4.41  tff(c_4274, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_4262])).
% 10.39/4.41  tff(c_4278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_30, c_28, c_26, c_4274])).
% 10.39/4.41  tff(c_4280, plain, (v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_4252])).
% 10.39/4.41  tff(c_4133, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | r5_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_3976])).
% 10.39/4.41  tff(c_4339, plain, (r5_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4280, c_4133])).
% 10.39/4.41  tff(c_24, plain, (![B_104, E_132, F_134, A_72, C_120, D_128]: (r5_binop_1(A_72, C_120, D_128) | ~r5_binop_1(k2_zfmisc_1(A_72, B_104), k6_filter_1(A_72, B_104, C_120, E_132), k6_filter_1(A_72, B_104, D_128, F_134)) | ~m1_subset_1(F_134, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_104, B_104), B_104))) | ~v1_funct_2(F_134, k2_zfmisc_1(B_104, B_104), B_104) | ~v1_funct_1(F_134) | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_104, B_104), B_104))) | ~v1_funct_2(E_132, k2_zfmisc_1(B_104, B_104), B_104) | ~v1_funct_1(E_132) | ~m1_subset_1(D_128, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_72, A_72), A_72))) | ~v1_funct_2(D_128, k2_zfmisc_1(A_72, A_72), A_72) | ~v1_funct_1(D_128) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_72, A_72), A_72))) | ~v1_funct_2(C_120, k2_zfmisc_1(A_72, A_72), A_72) | ~v1_funct_1(C_120) | v1_xboole_0(B_104) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_144])).
% 10.39/4.41  tff(c_4345, plain, (r5_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_4339, c_24])).
% 10.39/4.41  tff(c_4352, plain, (r5_binop_1('#skF_1', '#skF_3', '#skF_4') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_38, c_36, c_34, c_32, c_30, c_28, c_26, c_4345])).
% 10.39/4.41  tff(c_4354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_1326, c_4352])).
% 10.39/4.41  tff(c_4355, plain, (~r6_binop_1('#skF_2', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_68])).
% 10.39/4.41  tff(c_4498, plain, (![A_716, B_717, C_718]: (r6_binop_1(A_716, B_717, C_718) | ~r5_binop_1(A_716, B_717, C_718) | ~r4_binop_1(A_716, B_717, C_718) | ~m1_subset_1(C_718, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_716, A_716), A_716))) | ~v1_funct_2(C_718, k2_zfmisc_1(A_716, A_716), A_716) | ~v1_funct_1(C_718) | ~m1_subset_1(B_717, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_716, A_716), A_716))) | ~v1_funct_2(B_717, k2_zfmisc_1(A_716, A_716), A_716) | ~v1_funct_1(B_717))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.39/4.41  tff(c_4502, plain, (![B_717]: (r6_binop_1('#skF_2', B_717, '#skF_6') | ~r5_binop_1('#skF_2', B_717, '#skF_6') | ~r4_binop_1('#skF_2', B_717, '#skF_6') | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(B_717, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2(B_717, k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1(B_717))), inference(resolution, [status(thm)], [c_26, c_4498])).
% 10.39/4.41  tff(c_4535, plain, (![B_724]: (r6_binop_1('#skF_2', B_724, '#skF_6') | ~r5_binop_1('#skF_2', B_724, '#skF_6') | ~r4_binop_1('#skF_2', B_724, '#skF_6') | ~m1_subset_1(B_724, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2(B_724, k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1(B_724))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_4502])).
% 10.39/4.41  tff(c_4541, plain, (r6_binop_1('#skF_2', '#skF_5', '#skF_6') | ~r5_binop_1('#skF_2', '#skF_5', '#skF_6') | ~r4_binop_1('#skF_2', '#skF_5', '#skF_6') | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_4535])).
% 10.39/4.41  tff(c_4547, plain, (r6_binop_1('#skF_2', '#skF_5', '#skF_6') | ~r5_binop_1('#skF_2', '#skF_5', '#skF_6') | ~r4_binop_1('#skF_2', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_4541])).
% 10.39/4.41  tff(c_4548, plain, (~r5_binop_1('#skF_2', '#skF_5', '#skF_6') | ~r4_binop_1('#skF_2', '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_4355, c_4547])).
% 10.39/4.41  tff(c_4549, plain, (~r4_binop_1('#skF_2', '#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_4548])).
% 10.39/4.41  tff(c_4357, plain, (![A_698, B_699, C_700, D_701]: (v1_funct_1(k6_filter_1(A_698, B_699, C_700, D_701)) | ~m1_subset_1(D_701, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_699, B_699), B_699))) | ~v1_funct_2(D_701, k2_zfmisc_1(B_699, B_699), B_699) | ~v1_funct_1(D_701) | ~m1_subset_1(C_700, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_698, A_698), A_698))) | ~v1_funct_2(C_700, k2_zfmisc_1(A_698, A_698), A_698) | ~v1_funct_1(C_700))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.39/4.41  tff(c_4361, plain, (![A_698, C_700]: (v1_funct_1(k6_filter_1(A_698, '#skF_2', C_700, '#skF_6')) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_700, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_698, A_698), A_698))) | ~v1_funct_2(C_700, k2_zfmisc_1(A_698, A_698), A_698) | ~v1_funct_1(C_700))), inference(resolution, [status(thm)], [c_26, c_4357])).
% 10.39/4.41  tff(c_4437, plain, (![A_709, C_710]: (v1_funct_1(k6_filter_1(A_709, '#skF_2', C_710, '#skF_6')) | ~m1_subset_1(C_710, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_709, A_709), A_709))) | ~v1_funct_2(C_710, k2_zfmisc_1(A_709, A_709), A_709) | ~v1_funct_1(C_710))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_4361])).
% 10.39/4.41  tff(c_4446, plain, (v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_4437])).
% 10.39/4.41  tff(c_4458, plain, (v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_4446])).
% 10.39/4.41  tff(c_4365, plain, (![A_698, C_700]: (v1_funct_1(k6_filter_1(A_698, '#skF_2', C_700, '#skF_5')) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1(C_700, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_698, A_698), A_698))) | ~v1_funct_2(C_700, k2_zfmisc_1(A_698, A_698), A_698) | ~v1_funct_1(C_700))), inference(resolution, [status(thm)], [c_32, c_4357])).
% 10.39/4.42  tff(c_4403, plain, (![A_704, C_705]: (v1_funct_1(k6_filter_1(A_704, '#skF_2', C_705, '#skF_5')) | ~m1_subset_1(C_705, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_704, A_704), A_704))) | ~v1_funct_2(C_705, k2_zfmisc_1(A_704, A_704), A_704) | ~v1_funct_1(C_705))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_4365])).
% 10.39/4.42  tff(c_4406, plain, (v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_4403])).
% 10.39/4.42  tff(c_4418, plain, (v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_4406])).
% 10.39/4.42  tff(c_4428, plain, (![A_706, B_707, C_708]: (r4_binop_1(A_706, B_707, C_708) | ~r6_binop_1(A_706, B_707, C_708) | ~m1_subset_1(C_708, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_706, A_706), A_706))) | ~v1_funct_2(C_708, k2_zfmisc_1(A_706, A_706), A_706) | ~v1_funct_1(C_708) | ~m1_subset_1(B_707, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_706, A_706), A_706))) | ~v1_funct_2(B_707, k2_zfmisc_1(A_706, A_706), A_706) | ~v1_funct_1(B_707))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.39/4.42  tff(c_4436, plain, (r4_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_65, c_4428])).
% 10.39/4.42  tff(c_4752, plain, (r4_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4418, c_4458, c_4436])).
% 10.39/4.42  tff(c_4753, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_4752])).
% 10.39/4.42  tff(c_4756, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_4753])).
% 10.39/4.42  tff(c_4760, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_36, c_34, c_32, c_4756])).
% 10.39/4.42  tff(c_4761, plain, (~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | r4_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_4752])).
% 10.39/4.42  tff(c_5219, plain, (~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(splitLeft, [status(thm)], [c_4761])).
% 10.39/4.42  tff(c_5222, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_5219])).
% 10.39/4.42  tff(c_5226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_30, c_28, c_26, c_5222])).
% 10.39/4.42  tff(c_5228, plain, (m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(splitRight, [status(thm)], [c_4761])).
% 10.39/4.42  tff(c_4363, plain, (![A_698, C_700]: (v1_funct_1(k6_filter_1(A_698, '#skF_1', C_700, '#skF_4')) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1(C_700, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_698, A_698), A_698))) | ~v1_funct_2(C_700, k2_zfmisc_1(A_698, A_698), A_698) | ~v1_funct_1(C_700))), inference(resolution, [status(thm)], [c_38, c_4357])).
% 10.39/4.42  tff(c_4374, plain, (![A_698, C_700]: (v1_funct_1(k6_filter_1(A_698, '#skF_1', C_700, '#skF_4')) | ~m1_subset_1(C_700, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_698, A_698), A_698))) | ~v1_funct_2(C_700, k2_zfmisc_1(A_698, A_698), A_698) | ~v1_funct_1(C_700))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_4363])).
% 10.39/4.42  tff(c_5285, plain, (v1_funct_1(k6_filter_1(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_1', k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), '#skF_4')) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_5228, c_4374])).
% 10.39/4.42  tff(c_5359, plain, (v1_funct_1(k6_filter_1(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_1', k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), '#skF_4')) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4458, c_5285])).
% 10.39/4.42  tff(c_5372, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_5359])).
% 10.39/4.42  tff(c_5410, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_5372])).
% 10.39/4.42  tff(c_5414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_30, c_28, c_26, c_5410])).
% 10.39/4.42  tff(c_5416, plain, (v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_5359])).
% 10.39/4.42  tff(c_5227, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | r4_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_4761])).
% 10.39/4.42  tff(c_5417, plain, (~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(splitLeft, [status(thm)], [c_5227])).
% 10.39/4.42  tff(c_5431, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_5417])).
% 10.39/4.42  tff(c_5435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_36, c_34, c_32, c_5431])).
% 10.39/4.42  tff(c_5436, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | r4_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_5227])).
% 10.39/4.42  tff(c_5675, plain, (r4_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5416, c_5436])).
% 10.39/4.42  tff(c_16, plain, (![F_71, C_57, E_69, D_65, B_41, A_9]: (r4_binop_1(B_41, E_69, F_71) | ~r4_binop_1(k2_zfmisc_1(A_9, B_41), k6_filter_1(A_9, B_41, C_57, E_69), k6_filter_1(A_9, B_41, D_65, F_71)) | ~m1_subset_1(F_71, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_41, B_41), B_41))) | ~v1_funct_2(F_71, k2_zfmisc_1(B_41, B_41), B_41) | ~v1_funct_1(F_71) | ~m1_subset_1(E_69, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_41, B_41), B_41))) | ~v1_funct_2(E_69, k2_zfmisc_1(B_41, B_41), B_41) | ~v1_funct_1(E_69) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9, A_9), A_9))) | ~v1_funct_2(D_65, k2_zfmisc_1(A_9, A_9), A_9) | ~v1_funct_1(D_65) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9, A_9), A_9))) | ~v1_funct_2(C_57, k2_zfmisc_1(A_9, A_9), A_9) | ~v1_funct_1(C_57) | v1_xboole_0(B_41) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.39/4.42  tff(c_5678, plain, (r4_binop_1('#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_5675, c_16])).
% 10.39/4.42  tff(c_5684, plain, (r4_binop_1('#skF_2', '#skF_5', '#skF_6') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_38, c_36, c_34, c_32, c_30, c_28, c_26, c_5678])).
% 10.39/4.42  tff(c_5686, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_4549, c_5684])).
% 10.39/4.42  tff(c_5687, plain, (~r5_binop_1('#skF_2', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_4548])).
% 10.39/4.42  tff(c_5743, plain, (r4_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4418, c_4458, c_4436])).
% 10.39/4.42  tff(c_5744, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_5743])).
% 10.39/4.42  tff(c_5747, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_5744])).
% 10.39/4.42  tff(c_5751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_36, c_34, c_32, c_5747])).
% 10.39/4.42  tff(c_5753, plain, (v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_5743])).
% 10.39/4.42  tff(c_5752, plain, (~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | r4_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_5743])).
% 10.39/4.42  tff(c_6399, plain, (~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(splitLeft, [status(thm)], [c_5752])).
% 10.39/4.42  tff(c_6402, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_6399])).
% 10.39/4.42  tff(c_6406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_30, c_28, c_26, c_6402])).
% 10.39/4.42  tff(c_6408, plain, (m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(splitRight, [status(thm)], [c_5752])).
% 10.39/4.42  tff(c_4359, plain, (![A_698, C_700]: (v1_funct_1(k6_filter_1(A_698, '#skF_1', C_700, '#skF_3')) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_700, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_698, A_698), A_698))) | ~v1_funct_2(C_700, k2_zfmisc_1(A_698, A_698), A_698) | ~v1_funct_1(C_700))), inference(resolution, [status(thm)], [c_44, c_4357])).
% 10.39/4.42  tff(c_4368, plain, (![A_698, C_700]: (v1_funct_1(k6_filter_1(A_698, '#skF_1', C_700, '#skF_3')) | ~m1_subset_1(C_700, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_698, A_698), A_698))) | ~v1_funct_2(C_700, k2_zfmisc_1(A_698, A_698), A_698) | ~v1_funct_1(C_700))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_4359])).
% 10.39/4.42  tff(c_6512, plain, (v1_funct_1(k6_filter_1(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_1', k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), '#skF_3')) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_6408, c_4368])).
% 10.39/4.42  tff(c_6595, plain, (v1_funct_1(k6_filter_1(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_1', k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), '#skF_3')) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4458, c_6512])).
% 10.39/4.42  tff(c_6599, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_6595])).
% 10.39/4.42  tff(c_6603, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_6599])).
% 10.39/4.42  tff(c_6607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_30, c_28, c_26, c_6603])).
% 10.39/4.42  tff(c_6609, plain, (v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_6595])).
% 10.39/4.42  tff(c_6407, plain, (~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | r4_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_5752])).
% 10.39/4.42  tff(c_6657, plain, (~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | r4_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6609, c_6407])).
% 10.39/4.42  tff(c_6658, plain, (~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(splitLeft, [status(thm)], [c_6657])).
% 10.39/4.42  tff(c_6661, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_6658])).
% 10.39/4.42  tff(c_6665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_36, c_34, c_32, c_6661])).
% 10.39/4.42  tff(c_6667, plain, (m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(splitRight, [status(thm)], [c_6657])).
% 10.39/4.42  tff(c_4462, plain, (![A_711, B_712, C_713]: (r5_binop_1(A_711, B_712, C_713) | ~r6_binop_1(A_711, B_712, C_713) | ~m1_subset_1(C_713, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_711, A_711), A_711))) | ~v1_funct_2(C_713, k2_zfmisc_1(A_711, A_711), A_711) | ~v1_funct_1(C_713) | ~m1_subset_1(B_712, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_711, A_711), A_711))) | ~v1_funct_2(B_712, k2_zfmisc_1(A_711, A_711), A_711) | ~v1_funct_1(B_712))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.39/4.42  tff(c_4466, plain, (r5_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_65, c_4462])).
% 10.39/4.42  tff(c_4472, plain, (r5_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')) | ~v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~m1_subset_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2')))) | ~v1_funct_2(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4418, c_4466])).
% 10.39/4.42  tff(c_6884, plain, (r5_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5753, c_6667, c_4458, c_6609, c_6408, c_4472])).
% 10.39/4.42  tff(c_22, plain, (![B_104, E_132, F_134, A_72, C_120, D_128]: (r5_binop_1(B_104, E_132, F_134) | ~r5_binop_1(k2_zfmisc_1(A_72, B_104), k6_filter_1(A_72, B_104, C_120, E_132), k6_filter_1(A_72, B_104, D_128, F_134)) | ~m1_subset_1(F_134, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_104, B_104), B_104))) | ~v1_funct_2(F_134, k2_zfmisc_1(B_104, B_104), B_104) | ~v1_funct_1(F_134) | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_104, B_104), B_104))) | ~v1_funct_2(E_132, k2_zfmisc_1(B_104, B_104), B_104) | ~v1_funct_1(E_132) | ~m1_subset_1(D_128, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_72, A_72), A_72))) | ~v1_funct_2(D_128, k2_zfmisc_1(A_72, A_72), A_72) | ~v1_funct_1(D_128) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_72, A_72), A_72))) | ~v1_funct_2(C_120, k2_zfmisc_1(A_72, A_72), A_72) | ~v1_funct_1(C_120) | v1_xboole_0(B_104) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_144])).
% 10.39/4.42  tff(c_6887, plain, (r5_binop_1('#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_6884, c_22])).
% 10.39/4.42  tff(c_6893, plain, (r5_binop_1('#skF_2', '#skF_5', '#skF_6') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_38, c_36, c_34, c_32, c_30, c_28, c_26, c_6887])).
% 10.39/4.42  tff(c_6895, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_5687, c_6893])).
% 10.39/4.42  tff(c_6897, plain, (~r6_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_62])).
% 10.39/4.42  tff(c_64, plain, (r6_binop_1('#skF_1', '#skF_3', '#skF_4') | r6_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 10.39/4.42  tff(c_6898, plain, (r6_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_6897, c_64])).
% 10.39/4.42  tff(c_7008, plain, (![A_993, B_994, C_995]: (r5_binop_1(A_993, B_994, C_995) | ~r6_binop_1(A_993, B_994, C_995) | ~m1_subset_1(C_995, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_993, A_993), A_993))) | ~v1_funct_2(C_995, k2_zfmisc_1(A_993, A_993), A_993) | ~v1_funct_1(C_995) | ~m1_subset_1(B_994, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_993, A_993), A_993))) | ~v1_funct_2(B_994, k2_zfmisc_1(A_993, A_993), A_993) | ~v1_funct_1(B_994))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.39/4.42  tff(c_7010, plain, (r5_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_6898, c_7008])).
% 10.39/4.42  tff(c_7015, plain, (r5_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_38, c_7010])).
% 10.39/4.42  tff(c_6896, plain, (r6_binop_1('#skF_2', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_62])).
% 10.39/4.42  tff(c_7012, plain, (r5_binop_1('#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_6896, c_7008])).
% 10.39/4.42  tff(c_7018, plain, (r5_binop_1('#skF_2', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_28, c_26, c_7012])).
% 10.39/4.42  tff(c_20, plain, (![B_104, E_132, F_134, A_72, C_120, D_128]: (r5_binop_1(k2_zfmisc_1(A_72, B_104), k6_filter_1(A_72, B_104, C_120, E_132), k6_filter_1(A_72, B_104, D_128, F_134)) | ~r5_binop_1(B_104, E_132, F_134) | ~r5_binop_1(A_72, C_120, D_128) | ~m1_subset_1(F_134, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_104, B_104), B_104))) | ~v1_funct_2(F_134, k2_zfmisc_1(B_104, B_104), B_104) | ~v1_funct_1(F_134) | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_104, B_104), B_104))) | ~v1_funct_2(E_132, k2_zfmisc_1(B_104, B_104), B_104) | ~v1_funct_1(E_132) | ~m1_subset_1(D_128, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_72, A_72), A_72))) | ~v1_funct_2(D_128, k2_zfmisc_1(A_72, A_72), A_72) | ~v1_funct_1(D_128) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_72, A_72), A_72))) | ~v1_funct_2(C_120, k2_zfmisc_1(A_72, A_72), A_72) | ~v1_funct_1(C_120) | v1_xboole_0(B_104) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_144])).
% 10.39/4.42  tff(c_6947, plain, (![A_986, B_987, C_988]: (r4_binop_1(A_986, B_987, C_988) | ~r6_binop_1(A_986, B_987, C_988) | ~m1_subset_1(C_988, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_986, A_986), A_986))) | ~v1_funct_2(C_988, k2_zfmisc_1(A_986, A_986), A_986) | ~v1_funct_1(C_988) | ~m1_subset_1(B_987, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_986, A_986), A_986))) | ~v1_funct_2(B_987, k2_zfmisc_1(A_986, A_986), A_986) | ~v1_funct_1(B_987))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.39/4.42  tff(c_6949, plain, (r4_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_6898, c_6947])).
% 10.39/4.42  tff(c_6954, plain, (r4_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_38, c_6949])).
% 10.39/4.42  tff(c_6951, plain, (r4_binop_1('#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_6896, c_6947])).
% 10.39/4.42  tff(c_6957, plain, (r4_binop_1('#skF_2', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_28, c_26, c_6951])).
% 10.39/4.42  tff(c_14, plain, (![F_71, C_57, E_69, D_65, B_41, A_9]: (r4_binop_1(k2_zfmisc_1(A_9, B_41), k6_filter_1(A_9, B_41, C_57, E_69), k6_filter_1(A_9, B_41, D_65, F_71)) | ~r4_binop_1(B_41, E_69, F_71) | ~r4_binop_1(A_9, C_57, D_65) | ~m1_subset_1(F_71, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_41, B_41), B_41))) | ~v1_funct_2(F_71, k2_zfmisc_1(B_41, B_41), B_41) | ~v1_funct_1(F_71) | ~m1_subset_1(E_69, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_41, B_41), B_41))) | ~v1_funct_2(E_69, k2_zfmisc_1(B_41, B_41), B_41) | ~v1_funct_1(E_69) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9, A_9), A_9))) | ~v1_funct_2(D_65, k2_zfmisc_1(A_9, A_9), A_9) | ~v1_funct_1(D_65) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_9, A_9), A_9))) | ~v1_funct_2(C_57, k2_zfmisc_1(A_9, A_9), A_9) | ~v1_funct_1(C_57) | v1_xboole_0(B_41) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.39/4.42  tff(c_6901, plain, (![A_980, B_981, C_982, D_983]: (v1_funct_1(k6_filter_1(A_980, B_981, C_982, D_983)) | ~m1_subset_1(D_983, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_981, B_981), B_981))) | ~v1_funct_2(D_983, k2_zfmisc_1(B_981, B_981), B_981) | ~v1_funct_1(D_983) | ~m1_subset_1(C_982, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_980, A_980), A_980))) | ~v1_funct_2(C_982, k2_zfmisc_1(A_980, A_980), A_980) | ~v1_funct_1(C_982))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.39/4.42  tff(c_6909, plain, (![A_980, C_982]: (v1_funct_1(k6_filter_1(A_980, '#skF_2', C_982, '#skF_5')) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1(C_982, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_980, A_980), A_980))) | ~v1_funct_2(C_982, k2_zfmisc_1(A_980, A_980), A_980) | ~v1_funct_1(C_982))), inference(resolution, [status(thm)], [c_32, c_6901])).
% 10.39/4.42  tff(c_6983, plain, (![A_991, C_992]: (v1_funct_1(k6_filter_1(A_991, '#skF_2', C_992, '#skF_5')) | ~m1_subset_1(C_992, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_991, A_991), A_991))) | ~v1_funct_2(C_992, k2_zfmisc_1(A_991, A_991), A_991) | ~v1_funct_1(C_992))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_6909])).
% 10.39/4.42  tff(c_6986, plain, (v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_6983])).
% 10.39/4.42  tff(c_6998, plain, (v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_6986])).
% 10.39/4.42  tff(c_6905, plain, (![A_980, C_982]: (v1_funct_1(k6_filter_1(A_980, '#skF_2', C_982, '#skF_6')) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_982, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_980, A_980), A_980))) | ~v1_funct_2(C_982, k2_zfmisc_1(A_980, A_980), A_980) | ~v1_funct_1(C_982))), inference(resolution, [status(thm)], [c_26, c_6901])).
% 10.39/4.42  tff(c_6958, plain, (![A_989, C_990]: (v1_funct_1(k6_filter_1(A_989, '#skF_2', C_990, '#skF_6')) | ~m1_subset_1(C_990, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_989, A_989), A_989))) | ~v1_funct_2(C_990, k2_zfmisc_1(A_989, A_989), A_989) | ~v1_funct_1(C_990))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_6905])).
% 10.39/4.42  tff(c_6967, plain, (v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_6958])).
% 10.39/4.42  tff(c_6979, plain, (v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_6967])).
% 10.39/4.42  tff(c_7124, plain, (![A_1009, B_1010, C_1011, D_1012]: (m1_subset_1(k6_filter_1(A_1009, B_1010, C_1011, D_1012), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1009, B_1010), k2_zfmisc_1(A_1009, B_1010)), k2_zfmisc_1(A_1009, B_1010)))) | ~m1_subset_1(D_1012, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_1010, B_1010), B_1010))) | ~v1_funct_2(D_1012, k2_zfmisc_1(B_1010, B_1010), B_1010) | ~v1_funct_1(D_1012) | ~m1_subset_1(C_1011, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1009, A_1009), A_1009))) | ~v1_funct_2(C_1011, k2_zfmisc_1(A_1009, A_1009), A_1009) | ~v1_funct_1(C_1011))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.39/4.42  tff(c_2, plain, (![A_1, B_2, C_4]: (r6_binop_1(A_1, B_2, C_4) | ~r5_binop_1(A_1, B_2, C_4) | ~r4_binop_1(A_1, B_2, C_4) | ~m1_subset_1(C_4, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1, A_1), A_1))) | ~v1_funct_2(C_4, k2_zfmisc_1(A_1, A_1), A_1) | ~v1_funct_1(C_4) | ~m1_subset_1(B_2, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1, A_1), A_1))) | ~v1_funct_2(B_2, k2_zfmisc_1(A_1, A_1), A_1) | ~v1_funct_1(B_2))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.39/4.42  tff(c_7666, plain, (![B_1115, A_1113, C_1114, D_1117, B_1116]: (r6_binop_1(k2_zfmisc_1(A_1113, B_1115), B_1116, k6_filter_1(A_1113, B_1115, C_1114, D_1117)) | ~r5_binop_1(k2_zfmisc_1(A_1113, B_1115), B_1116, k6_filter_1(A_1113, B_1115, C_1114, D_1117)) | ~r4_binop_1(k2_zfmisc_1(A_1113, B_1115), B_1116, k6_filter_1(A_1113, B_1115, C_1114, D_1117)) | ~v1_funct_2(k6_filter_1(A_1113, B_1115, C_1114, D_1117), k2_zfmisc_1(k2_zfmisc_1(A_1113, B_1115), k2_zfmisc_1(A_1113, B_1115)), k2_zfmisc_1(A_1113, B_1115)) | ~v1_funct_1(k6_filter_1(A_1113, B_1115, C_1114, D_1117)) | ~m1_subset_1(B_1116, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1113, B_1115), k2_zfmisc_1(A_1113, B_1115)), k2_zfmisc_1(A_1113, B_1115)))) | ~v1_funct_2(B_1116, k2_zfmisc_1(k2_zfmisc_1(A_1113, B_1115), k2_zfmisc_1(A_1113, B_1115)), k2_zfmisc_1(A_1113, B_1115)) | ~v1_funct_1(B_1116) | ~m1_subset_1(D_1117, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_1115, B_1115), B_1115))) | ~v1_funct_2(D_1117, k2_zfmisc_1(B_1115, B_1115), B_1115) | ~v1_funct_1(D_1117) | ~m1_subset_1(C_1114, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1113, A_1113), A_1113))) | ~v1_funct_2(C_1114, k2_zfmisc_1(A_1113, A_1113), A_1113) | ~v1_funct_1(C_1114))), inference(resolution, [status(thm)], [c_7124, c_2])).
% 10.39/4.42  tff(c_7834, plain, (![B_1137, A_1140, C_1139, B_1138, D_1136]: (r6_binop_1(k2_zfmisc_1(A_1140, B_1138), B_1137, k6_filter_1(A_1140, B_1138, C_1139, D_1136)) | ~r5_binop_1(k2_zfmisc_1(A_1140, B_1138), B_1137, k6_filter_1(A_1140, B_1138, C_1139, D_1136)) | ~r4_binop_1(k2_zfmisc_1(A_1140, B_1138), B_1137, k6_filter_1(A_1140, B_1138, C_1139, D_1136)) | ~v1_funct_1(k6_filter_1(A_1140, B_1138, C_1139, D_1136)) | ~m1_subset_1(B_1137, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1140, B_1138), k2_zfmisc_1(A_1140, B_1138)), k2_zfmisc_1(A_1140, B_1138)))) | ~v1_funct_2(B_1137, k2_zfmisc_1(k2_zfmisc_1(A_1140, B_1138), k2_zfmisc_1(A_1140, B_1138)), k2_zfmisc_1(A_1140, B_1138)) | ~v1_funct_1(B_1137) | ~m1_subset_1(D_1136, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_1138, B_1138), B_1138))) | ~v1_funct_2(D_1136, k2_zfmisc_1(B_1138, B_1138), B_1138) | ~v1_funct_1(D_1136) | ~m1_subset_1(C_1139, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1140, A_1140), A_1140))) | ~v1_funct_2(C_1139, k2_zfmisc_1(A_1140, A_1140), A_1140) | ~v1_funct_1(C_1139))), inference(resolution, [status(thm)], [c_10, c_7666])).
% 10.39/4.42  tff(c_8175, plain, (![B_1180, D_1179, C_1181, A_1183, C_1182, D_1184]: (r6_binop_1(k2_zfmisc_1(A_1183, B_1180), k6_filter_1(A_1183, B_1180, C_1182, D_1179), k6_filter_1(A_1183, B_1180, C_1181, D_1184)) | ~r5_binop_1(k2_zfmisc_1(A_1183, B_1180), k6_filter_1(A_1183, B_1180, C_1182, D_1179), k6_filter_1(A_1183, B_1180, C_1181, D_1184)) | ~r4_binop_1(k2_zfmisc_1(A_1183, B_1180), k6_filter_1(A_1183, B_1180, C_1182, D_1179), k6_filter_1(A_1183, B_1180, C_1181, D_1184)) | ~v1_funct_1(k6_filter_1(A_1183, B_1180, C_1181, D_1184)) | ~v1_funct_2(k6_filter_1(A_1183, B_1180, C_1182, D_1179), k2_zfmisc_1(k2_zfmisc_1(A_1183, B_1180), k2_zfmisc_1(A_1183, B_1180)), k2_zfmisc_1(A_1183, B_1180)) | ~v1_funct_1(k6_filter_1(A_1183, B_1180, C_1182, D_1179)) | ~m1_subset_1(D_1184, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_1180, B_1180), B_1180))) | ~v1_funct_2(D_1184, k2_zfmisc_1(B_1180, B_1180), B_1180) | ~v1_funct_1(D_1184) | ~m1_subset_1(C_1181, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1183, A_1183), A_1183))) | ~v1_funct_2(C_1181, k2_zfmisc_1(A_1183, A_1183), A_1183) | ~v1_funct_1(C_1181) | ~m1_subset_1(D_1179, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_1180, B_1180), B_1180))) | ~v1_funct_2(D_1179, k2_zfmisc_1(B_1180, B_1180), B_1180) | ~v1_funct_1(D_1179) | ~m1_subset_1(C_1182, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1183, A_1183), A_1183))) | ~v1_funct_2(C_1182, k2_zfmisc_1(A_1183, A_1183), A_1183) | ~v1_funct_1(C_1182))), inference(resolution, [status(thm)], [c_8, c_7834])).
% 10.39/4.42  tff(c_8904, plain, (![B_1330, D_1334, C_1332, C_1331, A_1333, D_1329]: (r6_binop_1(k2_zfmisc_1(A_1333, B_1330), k6_filter_1(A_1333, B_1330, C_1332, D_1329), k6_filter_1(A_1333, B_1330, C_1331, D_1334)) | ~r5_binop_1(k2_zfmisc_1(A_1333, B_1330), k6_filter_1(A_1333, B_1330, C_1332, D_1329), k6_filter_1(A_1333, B_1330, C_1331, D_1334)) | ~r4_binop_1(k2_zfmisc_1(A_1333, B_1330), k6_filter_1(A_1333, B_1330, C_1332, D_1329), k6_filter_1(A_1333, B_1330, C_1331, D_1334)) | ~v1_funct_1(k6_filter_1(A_1333, B_1330, C_1331, D_1334)) | ~v1_funct_1(k6_filter_1(A_1333, B_1330, C_1332, D_1329)) | ~m1_subset_1(D_1334, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_1330, B_1330), B_1330))) | ~v1_funct_2(D_1334, k2_zfmisc_1(B_1330, B_1330), B_1330) | ~v1_funct_1(D_1334) | ~m1_subset_1(C_1331, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1333, A_1333), A_1333))) | ~v1_funct_2(C_1331, k2_zfmisc_1(A_1333, A_1333), A_1333) | ~v1_funct_1(C_1331) | ~m1_subset_1(D_1329, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B_1330, B_1330), B_1330))) | ~v1_funct_2(D_1329, k2_zfmisc_1(B_1330, B_1330), B_1330) | ~v1_funct_1(D_1329) | ~m1_subset_1(C_1332, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_1333, A_1333), A_1333))) | ~v1_funct_2(C_1332, k2_zfmisc_1(A_1333, A_1333), A_1333) | ~v1_funct_1(C_1332))), inference(resolution, [status(thm)], [c_10, c_8175])).
% 10.39/4.42  tff(c_8911, plain, (~r5_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~r4_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~v1_funct_1(k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_8904, c_6897])).
% 10.39/4.42  tff(c_8916, plain, (~r5_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6')) | ~r4_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_36, c_34, c_32, c_42, c_40, c_38, c_30, c_28, c_26, c_6998, c_6979, c_8911])).
% 10.39/4.42  tff(c_8917, plain, (~r4_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(splitLeft, [status(thm)], [c_8916])).
% 10.39/4.42  tff(c_8920, plain, (~r4_binop_1('#skF_2', '#skF_5', '#skF_6') | ~r4_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_14, c_8917])).
% 10.39/4.42  tff(c_8923, plain, (v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_38, c_36, c_34, c_32, c_30, c_28, c_26, c_6954, c_6957, c_8920])).
% 10.39/4.42  tff(c_8925, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_8923])).
% 10.39/4.42  tff(c_8926, plain, (~r5_binop_1(k2_zfmisc_1('#skF_1', '#skF_2'), k6_filter_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_filter_1('#skF_1', '#skF_2', '#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_8916])).
% 10.39/4.42  tff(c_8930, plain, (~r5_binop_1('#skF_2', '#skF_5', '#skF_6') | ~r5_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_6', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2'))) | ~v1_funct_2('#skF_5', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_8926])).
% 10.39/4.42  tff(c_8933, plain, (v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_38, c_36, c_34, c_32, c_30, c_28, c_26, c_7015, c_7018, c_8930])).
% 10.39/4.42  tff(c_8935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_8933])).
% 10.39/4.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.39/4.42  
% 10.39/4.42  Inference rules
% 10.39/4.42  ----------------------
% 10.39/4.42  #Ref     : 0
% 10.39/4.42  #Sup     : 1575
% 10.39/4.42  #Fact    : 0
% 10.39/4.42  #Define  : 0
% 10.39/4.42  #Split   : 65
% 10.39/4.42  #Chain   : 0
% 10.39/4.42  #Close   : 0
% 10.39/4.42  
% 10.39/4.42  Ordering : KBO
% 10.39/4.42  
% 10.39/4.42  Simplification rules
% 10.39/4.42  ----------------------
% 10.39/4.42  #Subsume      : 40
% 10.39/4.42  #Demod        : 3622
% 10.39/4.42  #Tautology    : 99
% 10.39/4.42  #SimpNegUnit  : 16
% 10.39/4.42  #BackRed      : 0
% 10.39/4.42  
% 10.39/4.42  #Partial instantiations: 0
% 10.39/4.42  #Strategies tried      : 1
% 10.39/4.42  
% 10.39/4.42  Timing (in seconds)
% 10.39/4.42  ----------------------
% 10.39/4.42  Preprocessing        : 0.37
% 10.39/4.42  Parsing              : 0.19
% 10.39/4.42  CNF conversion       : 0.05
% 10.39/4.42  Main loop            : 3.23
% 10.39/4.42  Inferencing          : 1.06
% 10.39/4.42  Reduction            : 1.28
% 10.39/4.42  Demodulation         : 1.00
% 10.39/4.42  BG Simplification    : 0.06
% 10.39/4.42  Subsumption          : 0.66
% 10.39/4.42  Abstraction          : 0.08
% 10.39/4.42  MUC search           : 0.00
% 10.39/4.42  Cooper               : 0.00
% 10.39/4.42  Total                : 3.69
% 10.39/4.42  Index Insertion      : 0.00
% 10.39/4.42  Index Deletion       : 0.00
% 10.39/4.42  Index Matching       : 0.00
% 10.39/4.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
